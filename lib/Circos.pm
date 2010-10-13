package Circos;

our $VERSION = '0.52';

=pod

=head1 NAME

Circos - Circular data visualizations for comparison of genomes, among other things

=head1 SYNOPSIS

    use Circos;
    Circos->run( %OPTIONS );

=head1 DESCRIPTION

Circos is a Perl application for the generation of
publication-quality, circularly composited renditions of genomic data
and related annotations.

Circos is particularly suited for visualizing alignments, conservation
and intra and inter-chromosomal relationships. However, Circos can be
used to plot any kind of 2D data in a circular layout - its use is not
limited to genomics. Circos' use of lines to relate position pairs
(ribbons add a thickness parameter to each end) is effective to
display relationships between objects or positions on one or more
scales.

Presently all documentation is in the form of tutorials at
http://mkweb.bcgsc.ca/circos.

=head1 IMPLEMENTATION

At this time, the module does not return any value, nor does it allow
for dynamic manipulation of the image creation process.

Pass in configuration parameters to generate an image. To create
another image, call run again with different options.

=head1 VERSION

Version 0.52.

=head1 FUNCTIONS/METHODS

=cut

# -------------------------------------------------------------------

use strict;
#use warnings;
use Carp qw( carp confess croak );
use Config::General;
use Data::Dumper;
use File::Basename;
use File::Spec::Functions;
use FindBin;
use GD::Polyline;
use GD;
use Getopt::Long;
use IO::File;
use List::Util qw( max min );
use Math::Bezier;
use Math::BigFloat;
use Math::Round qw(round nearest);
use Math::VecStat qw(sum average);
use Memoize;
use POSIX qw(atan);
use Params::Validate qw(:all);
use Pod::Usage;
use Readonly;
use Set::IntSpan 1.11 qw(map_set);
use Storable qw(dclone); 

use lib "$FindBin::RealBin";
use lib "$FindBin::RealBin/../lib";
use lib "$FindBin::RealBin/lib";

Readonly my $APP_NAME   => 'circos';
Readonly my $CARAT      => q{^};
Readonly my $COLON      => q{:};
Readonly my $COMMA      => q{,};
Readonly my $DASH       => q{-};
Readonly my $DEG2RAD    => 0.0174532925;
Readonly my $DOLLAR     => q{$};
Readonly my $EMPTY_STR  => q{};
Readonly my $EQUAL_SIGN => q{=};
Readonly my $PI         => 3.141592654;
Readonly my $PIPE       => q{|};
Readonly my $PLUS_SIGN  => q{+};
Readonly my $RAD2DEG    => 57.29577951;
Readonly my $SEMICOLON  => q{;};
Readonly my $SPACE      => q{ };

# 
# Globals here
# 

my ( %OPT, %CONF, $DIMS, $IM, $IM_BRUSHES, $PNG_MAKE, $SVG_MAKE,
     $MAP_MAKE, @MAP_ELEMENTS,
     @IDEOGRAMS, $KARYOTYPE, $COLORS, $GCIRCUM );
my $GSIZE_NOSCALE = 0;

# -------------------------------------------------------------------

sub run {

=pod

  Circos->run( configfile => $file  );
  Circos->run( config     => \%CONF );

Runs the Circos code. You must pass either the "configfile" location
or a hashref of the configuration options.

=cut

  my $package = shift;

  %OPT = ref $_[0] eq 'HASH' ? %{ $_[0] } : @_;

  if ( $OPT{'configfile'} ) {
    loadconfiguration( $OPT{'configfile'} );
  } elsif ( $OPT{'config'} ) {
    %CONF = %{ $OPT{'config'} };
  } else {
    confess('No "configfile" or "config" parameter');
  }

  populateconfiguration(); # copy command line options to config hash
  validateconfiguration();

  if ( $CONF{debug} > 1 ) {
    $Data::Dumper::Pad       = "debug parameters";
    $Data::Dumper::Indent    = 1;
    $Data::Dumper::Quotekeys = 0;
    $Data::Dumper::Terse     = 1;
    printdebug(Dumper(\%CONF));
  }

  for my $f ( qw(ideogram_spacing unit_parse unit_strip 
		 getrelpos_scaled_ideogram_start )
	    ) {
    memoize($f);
  }

  my $outputfile = sprintf( "%s/%s",
			    $CONF{outputdir}  || $CONF{image}{dir},
			    $CONF{outputfile} || $CONF{image}{file} );
  $SVG_MAKE = $outputfile =~ /\.svg/;
  $PNG_MAKE = $outputfile =~ /\.png/;
  $outputfile =~ s/(.*)\..*/$1/;
  my $outputfile_svg = "$outputfile.svg";
  my $outputfile_png = "$outputfile.png";

  $SVG_MAKE = $CONF{image}{svg} if defined $CONF{image}{svg};
  $PNG_MAKE = $CONF{image}{png} if defined $CONF{image}{png};

  $PNG_MAKE = 1 if !$SVG_MAKE && !$PNG_MAKE;

  my $outputfile_map;
  if ( $CONF{image}{image_map_use} ) {
    $outputfile_map = $CONF{image}{image_map_file} || "$outputfile.html";
    if($outputfile_map !~ /\//) {
      $outputfile_map = sprintf("%s/%s",
				$CONF{outputdir}  || $CONF{image}{dir},
				$outputfile_map);
    }
    $MAP_MAKE = 1;
  }

  if ( $MAP_MAKE) {
    open MAP, ">$outputfile_map" or confess "Cannot write to the image map file $outputfile_map: $!\n";
    printf MAP "<map name='%s'>\n",
      $CONF{image}{image_map_name} || ($CONF{outputfile} || $CONF{image}{file})."html";
  }

  if ( $SVG_MAKE ) {
    open SVG, '>', $outputfile_svg 
      or confess "Can't write $outputfile_svg: $!\n";
  }

  printsvg(q{<?xml version="1.0" standalone="no"?>});
  printsvg(
	   q{<!DOCTYPE svg PUBLIC "-//W3C//DTD SVG 1.1//EN" "http://www.w3.org/Graphics/SVG/1.1/DTD/svg11.dtd">}
	  );

  ################################################################
  # Read karyotype and populate the KARYOTYPE data structure which
  # stores information about chromosomes and bands. 

  $KARYOTYPE = read_karyotype( file => $CONF{karyotype} );
  validate_karyotype( karyotype => $KARYOTYPE );
  printdebug("got cytogenetic information for",int( keys %$KARYOTYPE ),"chromosomes");

  #printdumper($KARYOTYPE);exit;

  ################################################################
  # determine the chromosomes to be shown and their regions;
  # if a chromosome region has not been defined (e.g. 15 vs 15:x-y)
  # then set the region to be the entire chromosome
  #
  # if no chromosomes are specified, all chromosomes from the karyotype file
  # are displayed if chromosomes_display_default is set
  #
  # hs1,hs2,hs3
  # hs1:10-20,hs2,hs3
  # -hs1:10-20,hs2,hs3
  # hs1:10-20,hs1:40-50,hs2,hs3
  #
  # the ideogram can have an optional label, which can be
  # used in the chromosomes_order field
  #
  # hs1[a],hs2[b],hs3[c]:10-20

  my @chrs = parse_chromosomes();

  # refine accept/reject regions by
  # - removing reject regions (defined by breaks) from accept regions
  # - make sure that the accept/reject regions are within the chromosome (perform intersection)

  refine_display_regions();

  # create a list of structures to draw in the image

  @IDEOGRAMS = grep( $_->{set}->cardinality > 1, create_ideogram_set(@chrs) );

  ################################################################
  # process chr scaling factor; you can scale chromosomes
  # to enlarge/shrink their extent on the image. Without scaling,
  # each ideogram will occupy a fraction of the circle (not counting
  # spaces between the ideograms) proportional to its total size. Thus
  # a 200Mb chromosome will always be twice as long as a 100Mb chromosome,
  # regardless of any non-linear scale adjustments.
  #
  # with scaling, you can make a 100Mb chromosome occupy the same
  # extent by using a scale of 2.

  register_chromosomes_scale() if $CONF{chromosomes_scale};

  ################################################################
  # direction of individual ideograms can be reversed
  # chromosomes_reverse = tag,tag

  register_chromosomes_direction() if $CONF{chromosomes_reverse};

  ################################################################
  # process the order of appearance of the chromosomes on the image
  #
  # chromosome names can be labels associated with individual ranges
  #
  # ^, -, -, hs3, hs1, -, hs2
  #
  # ^, -, -, a, c, -, b
  #
  # the process of deteriming the final order is convoluted

  #printdumper(@IDEOGRAMS);
  #printdumper($KARYOTYPE->{hs1}{chr});
  #exit;

  my @chrorder = read_chromosomes_order();
  #printdumper(@chrorder);exit;

  # construct ideogram groups based on the content of chromosomes_order, with
  # each group corresponding to a list of tags between breaks "|" in the
  # chromosomes_order string

  my $chrorder_groups = [ { idx => 0, cumulidx => 0 } ];
  $chrorder_groups = make_chrorder_groups($chrorder_groups, \@chrorder);
  
  #printdumper(@IDEOGRAMS);exit;
  #printdumper($chrorder_groups);exit;

  ################################################################
  #
  # Now comes the convoluted business. Here is where I set the display_idx
  # which is the order in which the ideograms are displayed.
  #
  # Iterate through each group, handling the those with start/end
  # anchors first, and assign the display_idx to each tag as follows
  #
  # - start at 0 if this is a group with start anchor
  # - start at num_ideograms (backwards) if this is a group with end anchor
  # - set display_idx <- ideogram_idx if this display_idx is not already defined
  #     (this anchors the position to be the same as the first placeable ideogram)
  #
  ################################################################
  set_display_index($chrorder_groups);

  #printdumper($chrorder_groups);exit;

  ################################################################
  #
  # now check each group and make sure that the display_idx values
  # don't overlap - if they do, shift each group (starting with
  # the first one that overlaps) until there is no more overlap
  #
  ################################################################

  reform_chrorder_groups($chrorder_groups);

  #print Dumper(@IDEOGRAMS);
  #printdumper($chrorder_groups);
  #exit;
  recompute_chrorder_groups($chrorder_groups);
  #printdumper($chrorder_groups);
  #exit;

  @IDEOGRAMS = sort { $a->{display_idx} <=> $b->{display_idx} } @IDEOGRAMS;
  
  # for each ideogram, record
  #  - prev/next ideogram
  #  - whether axis breaks may be required at ends

  for my $i ( 0 .. @IDEOGRAMS - 1 ) {
    my $this = $IDEOGRAMS[$i];
    next unless defined $this->{display_idx};
    my $next = $i < @IDEOGRAMS - 1 ? $IDEOGRAMS[ $i + 1 ] : $IDEOGRAMS[0];
    my $prev = $IDEOGRAMS[ $i - 1 ];

    #print Dumper($this);
    $this->{next} = $next;
    $this->{prev} = $prev;
    if (   $next->{chr} ne $this->{chr}
	   && $this->{set}->max < $KARYOTYPE->{ $this->{chr} }{chr}{set}->max ) {
      $this->{break}{end} = 1;
    }
    if (   $prev->{chr} ne $this->{chr}
	   && $this->{set}->min > $KARYOTYPE->{ $this->{chr} }{chr}{set}->min ) {
      $this->{break}{start} = 1;
    }
  }

  $CONF{chromosomes_units} = unit_convert(
					  from    => $CONF{chromosomes_units},
					  to      => 'b',
					  factors => {
						      nb => 1,
						      rb => 10**(
								 int(
								     log( sum( map { $_->{set}->cardinality } @IDEOGRAMS ) ) /
								     log(10)
								    )
								)
						     }
					 );

  ################################################################
  # non-linear scale

  my @zooms = make_list( $CONF{zooms}{zoom} );
  for my $zoom (@zooms) {
    my @param_path = ( $CONF{zooms} );
    unit_validate( $zoom->{start}, 'zoom/start', qw(u b) );
    unit_validate( $zoom->{end},   'zoom/end',   qw(u b) );
    for my $pos (qw(start end)) {
      $zoom->{$pos} = unit_convert(
				   from    => $zoom->{$pos},
				   to      => 'b',
				   factors => { ub => $CONF{chromosomes_units} }
				  );
    }
    $zoom->{set} = Set::IntSpan->new( sprintf( '%d-%d', $zoom->{start}, $zoom->{end} ) );
    my $smooth_distance = seek_parameter( 'smooth_distance', $zoom, @param_path );
    my $smooth_steps = seek_parameter( 'smooth_steps', $zoom, @param_path );
    next unless $smooth_distance && $smooth_steps;
    unit_validate( $smooth_distance, 'smooth_distance', qw(r u b) );
    $smooth_distance = unit_convert(from    => $smooth_distance,
				    to      => 'b',
				    factors => {ub => $CONF{chromosomes_units},
						rb => $zoom->{set}->cardinality}
				   );
    $zoom->{smooth}{distance} = $smooth_distance;
    $zoom->{smooth}{steps}    = $smooth_steps;
  }
  my $Gspans;
  for my $ideogram (@IDEOGRAMS) {

    my $chr = $ideogram->{chr};

    # create sets and level for zoom
    my @param_path = ( $CONF{zooms}{zoom} );

    # check which zooms apply to this ideogram
    my @ideogram_zooms = grep( $_->{chr} eq $ideogram->{chr}
			       && ( !defined $_->{use} || $_->{use} )
			       && $ideogram->{set}->intersect( $_->{set} )->cardinality,
			       @zooms );
    # construct a list of zoomed regions from smoothing parameters (smooth_distance, smooth_steps)
    my @zooms_smoothers;
    for my $zoom (@ideogram_zooms) {
      my $d = $zoom->{smooth}{distance};
      my $n = $zoom->{smooth}{steps};
      next unless $d && $n;
      my $subzoom_size = $d / $n;
      for my $i ( 1 .. $n ) {
	my $subzoom_scale = ( $zoom->{scale} * ( $n + 1 - $i ) + $ideogram->{scale} * $i ) / ( $n + 1 );
	#printinfo($d,$n,$subzoom_size,$i,$subzoom_scale);
	my $subzoom_start = $zoom->{set}->min - $i * $subzoom_size;
	my $subzoom_end   = $subzoom_start + $subzoom_size;
	push @zooms_smoothers,
	  {set => Set::IntSpan->new(sprintf( '%d-%d', $subzoom_start, $subzoom_end ))->intersect( $ideogram->{set} ),
	   scale => $subzoom_scale
	  };
	$subzoom_start = $zoom->{set}->max + ( $i - 1 ) * $subzoom_size;
	$subzoom_end = $subzoom_start + $subzoom_size;
	push @zooms_smoothers,
	  {set => Set::IntSpan->new(sprintf( '%d-%d', $subzoom_start, $subzoom_end ))->intersect( $ideogram->{set} ),
	   scale => $subzoom_scale
	  };
      }
    }
    push @ideogram_zooms, @zooms_smoothers if @zooms_smoothers;
    push @ideogram_zooms, {set => $ideogram->{set}, scale => $ideogram->{scale}, null => 1 };

    my %boundaries;
    for my $zoom (@ideogram_zooms) {
      for my $pos ($zoom->{set}->min-1,
		   $zoom->{set}->min,
		   $zoom->{set}->max,
		   $zoom->{set}->max+1
		  ) {
	$boundaries{$pos}++;
      }
    }
    my @boundaries = sort { $a <=> $b } keys %boundaries;

    # the first and last boundary are, by construction, outside of any
    # zoom set, so we are rejecting these
    @boundaries = @boundaries[ 1 .. @boundaries - 2 ];
    my @covers;
    for my $i ( 0 .. @boundaries - 2 ) {
      my ( $x, $y ) = @boundaries[ $i, $i + 1 ];
      my $cover = { set => Set::IntSpan->new("$x-$y") };
      $cover->{set} = $cover->{set}->intersect( $ideogram->{set} );
      next unless $cover->{set}->cardinality;
      for my $zoom (@ideogram_zooms) {
	if ( $zoom->{set}->intersect( $cover->{set} )->cardinality ) {
	  my $zoom_level = max( $zoom->{scale}, 1 / $zoom->{scale} );
	  if ( ! defined $cover->{level}
	       || ( !$zoom->{null} && $zoom_level > $cover->{level} ) ) {
	    $cover->{level} = $zoom_level;
	    $cover->{scale} = $zoom->{scale};
	  }
	}
      }
      my $merged;
      for my $c (@covers) {
	if (
	    $c->{level} == $cover->{level}
	    && $c->{scale} == $cover->{scale}
	    && (   ( $c->{set}->min == $cover->{set}->max )
		   || ( $c->{set}->max == $cover->{set}->min )
		   || (
		       $c->{set}->intersect( $cover->{set} )->cardinality )
	       )
	   ) {
	  $c->{set} = $c->{set}->union( $cover->{set} );
	  $merged = 1;
	  last;
	}
      }
      if ( !$merged ) {
	push @covers, $cover;
      }
    }
    # make sure that covers don't overlap
    my $prev_cover;
    for my $cover (@covers) {
      $cover->{set}->D($prev_cover->{set}) if $prev_cover;
      printinfo(
                sprintf(
			"zoomregion ideogram %d chr %s %9d %9d scale %5.2f absolutescale %5.2f",
			$ideogram->{idx},   $ideogram->{chr},
			$cover->{set}->min, $cover->{set}->max,
			$cover->{scale},    $cover->{level}
		       )
	       );
      $prev_cover = $cover;
    }

    # add up the zoomed distances for all zooms (zoom range * level) as well as size of all zooms
    my $sum_cover_sizescaled = sum( map { ( $_->{set}->cardinality ) * $_->{scale} } @covers );
    my $sum_cover_size = sum( map { ( $_->{set}->cardinality   ) } @covers );

    $ideogram->{covers}          = \@covers;
    $ideogram->{length}{scale}   = $sum_cover_sizescaled;
    $ideogram->{length}{noscale} = $ideogram->{set}->cardinality;
  }

  ################################################################
  # construct total size of all displayed ideograms and
  # cumulative size for each chromosome

  my $Gsize = 0;
  for my $ideogram (@IDEOGRAMS) {
    $ideogram->{length}{cumulative}{scale}   = $Gsize;
    $ideogram->{length}{cumulative}{noscale} = $GSIZE_NOSCALE;
    for my $cover ( @{ $ideogram->{covers} } ) {
      $Gsize += ( $cover->{set}->cardinality ) * $cover->{scale};
      $GSIZE_NOSCALE += ( $cover->{set}->cardinality );
    }
  }
  printdebug( "total displayed chromosome size", $GSIZE_NOSCALE );
  printdebug( "total displayed and scaled chromosome size", $Gsize );

  $DIMS->{image}{radius} = unit_strip( $CONF{image}{radius}, 'p' );
  $DIMS->{image}{width}  = 2 * $DIMS->{image}{radius};
  $DIMS->{image}{height} = 2 * $DIMS->{image}{radius};

  printdebug(
	     'creating image template for circle',
	     $DIMS->{image}{radius},
	     'px diameter'
	    );

  printsvg( qq{<svg width="$DIMS->{image}{width}px" height="$DIMS->{image}{height}px" version="1.1" xmlns="http://www.w3.org/2000/svg" xmlns:xlink="http://www.w3.org/1999/xlink">}
	  );

  register_chromosomes_radius();

  ################################################################
  # repeatedly creating brushes with color allocation can soak up
  # CPU time. This hash stores brushes of a given width/height size
  #
  # width=2 height=3 brush
  # $im_brushes->{size}{2}{3}

  my $bgfill;
  if ( locate_file( file => $CONF{image}{background}, return_undef => 1 ) ) {
    $IM = GD::Image->new( locate_file( file => $CONF{image}{background} ) );
  } else {
    eval {
      $IM = GD::Image->new( @{ $DIMS->{image} }{qw(height width)},
			    $CONF{image}{"24bit"} );
    };
    if ($@) {
      $IM = GD::Image->new( @{ $DIMS->{image} }{qw(height width)} );
    }
    $bgfill = 1;
  }

  $COLORS = allocate_colors( $IM, 1 ) if $PNG_MAKE;

  $IM->transparent( $COLORS->{transparent} ) if $PNG_MAKE;
  printdebug( "allocated", int( keys %$COLORS ), "colors" );
  $IM->fill( 0, 0, $COLORS->{ $CONF{image}{background} } )
    if $bgfill && $PNG_MAKE;

  ################################################################
  # GD TTF sanity check - text must be rendered correctly by each font
  
  for my $fontfile (map { locate_file(file=>$_) } values %{$CONF{fonts}}) {
    my $text = "abc";
    my @label_bounds = GD::Image->stringFT($COLORS->{black},
					   $fontfile,
					   10,
					   0, 0, 0, 
					   $text);
    my ( $label_width, $label_height ) = text_label_size(@label_bounds);
    if(! $label_width || ! $label_height) {
      confess "There was a problem with True Type font support. Circos could not render text from the font file $fontfile. Please check that gd (system graphics library) and GD (Perl's interface to gd) are compiled with True Type support.";
    }
  }

  $GCIRCUM = $Gsize;
  for my $i ( 0 .. @IDEOGRAMS - 1 ) {
    my $id1     = $IDEOGRAMS[$i];
    my $id2     = $IDEOGRAMS[ $i + 1 ] || $IDEOGRAMS[0];
    my $spacing = ideogram_spacing( $id1, $id2 );
    printinfo(
	      "ideogramspacing", $id1->{chr}, $id1->{tag},
	      $id2->{chr},       $id2->{tag}, $spacing
	     );
    $GCIRCUM += $spacing;
  }

  for my $ideogram (@IDEOGRAMS) {
    printinfo(
	      sprintf(
		      'ideogramreport %3d %5s %3d %5s %10.3f %10.3f %10.3f %11.3f %11.3f r %d %d %d %d',
		      $ideogram->{idx},
		      $ideogram->{chr},
		      $ideogram->{display_idx},
		      $ideogram->{tag},
		      $ideogram->{set}->min / 1e3,
		      $ideogram->{set}->max / 1e3,
		      $ideogram->{set}->size / 1e3,
		      $ideogram->{length}{cumulative}{noscale} / 1e3,
		      $ideogram->{length}{cumulative}{scale} / 1e3,
		      $ideogram->{radius},
		      $ideogram->{radius_inner},
		      $ideogram->{radius_outer},
		      $ideogram->{thickness},
		     )
	     );
    if ( $CONF{debug} ) {
      for (
	   my $pos = $ideogram->{set}->min ;
	   $pos <= $ideogram->{set}->max ;
	   $pos += $CONF{chromosomes_units}
	  ) {
	printdebug(
		   sprintf(
			   'ideogrampositionreport %2d %5s pos %9s angle %f r %d',
			   $ideogram->{idx}, $ideogram->{chr}, $pos,
			   getanglepos( $pos, $ideogram->{chr} )
			  )
		  );
      }
    }
  }

  # All data sets are stored in this structure. I'm making the
  # assumption that memory is not an issue.

  my $data;

  ################################################################
  #
  # chromosome ideograms and highlights
  #

  ################################################################
  #
  # Process data for highlights
  #
  # Highlights work differently than other data types, because they're
  # drawn underneath all othere data and figure elements,
  # including grids, tick marks and tick labels.
  #
  ################################################################

  $data->{highlights}{param} =
    parse_parameters( $CONF{highlights}, 'highlight' );

  for my $highlight_set ( make_list( $CONF{highlights}{highlight} ) ) {
    my @param_path = ( $highlight_set, $data->{highlights} );
    next
      unless !defined seek_parameter( 'show', @param_path )
	|| seek_parameter( 'show', @param_path );
    my $highlight_set_param =
      parse_parameters( $highlight_set, 'highlight', 0, 'file' );
    my $dataset = {};
    $dataset->{param} = $highlight_set_param;
    $dataset->{data}  = read_data_file(
				       locate_file( file => $highlight_set_param->{file} ),
				       'highlight',
				       {
					padding      => seek_parameter( 'padding',      @param_path ),
					minsize      => seek_parameter( 'minsize',      @param_path ),
					record_limit => seek_parameter( 'record_limit', @param_path )
				       },
				      );
    push @{ $data->{highlights}{dataset} }, $dataset;
  }

  # populates $data->{highlights}{param}{zlist}[ ]
  register_z_levels( $data->{highlights} );

  ################################################################
  #
  # Draw ideograms
  #
  ################################################################

  printsvg(qq{<g id="ideograms">}) if $SVG_MAKE;

  for my $ideogram (@IDEOGRAMS) {
    $ideogram->{set}->cardinality;
    # TODO - what was the point of this?
    #next if $ideogram->{set}->cardinality < 2; # CHECK THIS
    my $chr = $ideogram->{chr};
    my ( $start, $end ) = ( $ideogram->{set}->min, $ideogram->{set}->max );
    my ( $start_a, $end_a ) = ( getanglepos( $start, $chr ), getanglepos( $end, $chr ) );

    printdebug(sprintf('ideogram %s scale %f idx %d base_range %d %d angle_range %.3f %.3f',
		       $chr, $ideogram->{scale}, $ideogram->{display_idx},
		       $start, $end, $start_a, $end_a
		      )
	      );
    
    #printinfo("drawing highlights");
    draw_highlights( $data->{highlights}, $chr, $ideogram->{set}, $ideogram,
		     { ideogram => 0, layer_with_data => 0 } );
    #printinfo("done drawing highlights");
    
    # first pass at drawing ideogram - stroke and fill
    # TODO consider removing this if radius_from==radius_to

    my $url = seek_parameter("url",$ideogram) || $CONF{ideogram}{ideogram_url};
    #printdumper($ideogram);
    #printinfo($url);
    $url = format_url(url=>$url,param_path=>[$ideogram,
					     {start=>$ideogram->{set}->min,
					      end=>$ideogram->{set}->max,}
					    ]);
    #printinfo($url);
    slice(
	  image       => $IM,
	  start       => $start,
	  end         => $end,
	  chr         => $chr,
	  radius_from => $DIMS->{ideogram}{ $ideogram->{tag} }{radius_inner},
	  radius_to   => $DIMS->{ideogram}{ $ideogram->{tag} }{radius_outer},
	  edgecolor   => $CONF{ideogram}{stroke_color},
	  edgestroke  => $CONF{ideogram}{stroke_thickness},
	  fillcolor   => $CONF{ideogram}{fill} ? ( $KARYOTYPE->{$chr}{chr}{color} || $CONF{ideogram}{fill_color} ) : undef,
	  mapoptions => { url=>$url },
	 );

    if ( $CONF{ideogram}{show_label} ) {
      my $fontfile =
	$CONF{fonts}{ $CONF{ideogram}{label_font} || 'default' };
      $fontfile = locate_file( file => $fontfile );
      my $label = $KARYOTYPE->{$chr}{chr}{label};
      $label .= $ideogram->{tag} if $ideogram->{tag} ne $chr && $ideogram->{tag} !~ /__/ && $CONF{ideogram}{label_with_tag};
      my @label_bounds = GD::Image->stringFT(
					     $COLORS->{
						       seek_parameter( 'label_color', $CONF{ideogram} ) || 'black'
						      },
					     $fontfile,
					     unit_strip( $CONF{ideogram}{label_size}, 'p' ),
					     0, 0, 0, $label
					    );
      my ( $label_width, $label_height ) = text_label_size(@label_bounds);
      my $textangle = getanglepos( get_set_middle( $ideogram->{set} ), $chr );
      if ( seek_parameter( 'label_center', $CONF{ideogram} ) ) {
	$DIMS->{ideogram}{ $ideogram->{tag} }{label}{radius} -=
	  $label_width / 2;
      }
      my ( $offset_angle, $offset_radius ) =
	textoffset( $textangle,
		    $DIMS->{ideogram}{ $ideogram->{tag} }{label}{radius},
		    $label_width, $label_height,
		    0,
		    $CONF{ideogram}{label_parallel});
      my $pos = get_set_middle( $ideogram->{set} );
      draw_text(
                image => $IM,
                font  => $fontfile,
                color => seek_parameter( 'label_color', $CONF{ideogram} ) || 'black',
                size   => unit_strip( $CONF{ideogram}{label_size}, 'p' ),
                radius => $offset_radius + $DIMS->{ideogram}{ $ideogram->{tag} }{label}{radius},
                pangle => getanglepos( $pos, $chr ),
                angle => $DEG2RAD * ( $offset_angle + textangle($textangle,$CONF{ideogram}{label_parallel}) ),
                xy => [
		       getxypos(
				getanglepos( $pos, $chr ),
				$offset_radius +
				$DIMS->{ideogram}{ $ideogram->{tag} }{label}{radius}
			       )
		      ],
                svgxy => [
			  getxypos(
				   getanglepos( $pos, $chr ) +
				   $offset_angle / $CONF{svg_font_scale},
				   $CONF{ideogram}{label_parallel}*$offset_radius + $DIMS->{ideogram}{ $ideogram->{tag} }{label}{radius}
				  )
			 ],
                svgangle   => textanglesvg($textangle,$CONF{ideogram}{label_parallel}),
                text       => $label,
                chr        => $chr,
                start      => $pos,
                end        => $pos,
                mapoptions => { url=>$url }
	       );
    }

    # draw scale ticks
    if ( $CONF{show_ticks} ) {
      draw_ticks(ideogram         => $ideogram);
    } 

    # cytogenetic bands
    for my $band ( make_list( $KARYOTYPE->{$chr}{band} ) ) {
      next unless $CONF{ideogram}{show_bands};
      my ( $bandstart, $bandend ) = @{$band}{qw(start end)};
      my $bandset = $band->{set}->intersect( $ideogram->{set} );
      next unless $bandset->cardinality;
      my $fillcolor =
	$CONF{ideogram}{band_transparency}
	  ? sprintf( '%s_a%d',
		     $band->{color}, $CONF{ideogram}{band_transparency} )
	    : $band->{color};

      #printdumper($band) if $band->{name} eq "p31.1" && $band->{chr} eq "hs1";
      my $url = seek_parameter("url",$band) || $CONF{ideogram}{band_url};
      $url = format_url(url=>$url,param_path=>[$band->{options}||{},$band]);

      slice(
	    image       => $IM,
	    start       => $bandset->min,
	    end         => $bandset->max,
	    chr         => $chr,
	    radius_from => get_ideogram_radius($ideogram) -
	    $DIMS->{ideogram}{ $ideogram->{tag} }{thickness},
	    radius_to  => get_ideogram_radius($ideogram),
	    edgecolor  => $CONF{ideogram}{stroke_color},
	    edgestroke => $CONF{ideogram}{band_stroke_thickness},
	    mapoptions => { url=>$url },
	    fillcolor => $CONF{ideogram}{fill_bands} ? $fillcolor : undef
	   );
    }

    # ideogram highlights
    draw_highlights( $data->{highlights}, $chr, $ideogram->{set}, $ideogram,
		     {
		      ideogram => 1, layer_with_data => 0 } );

    # ideogram outline - stroke only, not filled
    # ideogram outline and label
    if($CONF{ideogram}{stroke_thickness}) {
      slice(
	    image       => $IM,
	    start       => $start,
	    end         => $end,
	    chr         => $chr,
	    radius_from => get_ideogram_radius($ideogram) -
	    $DIMS->{ideogram}{ $ideogram->{tag} }{thickness},
	    radius_to  => get_ideogram_radius($ideogram),
	    edgecolor  => $CONF{ideogram}{stroke_color},
	    edgestroke => $CONF{ideogram}{stroke_thickness},
	    fillcolor  => undef,
	   );
    }
  }

  for my $ideogram (@IDEOGRAMS) {
    if ( $ideogram->{chr} eq $ideogram->{next}{chr} || $ideogram->{break}{start} || $ideogram->{break}{end} ) {
      # v0.52 fixes problem with axis break display when a single
      # ideogram with a break was shown. The problem is due to the
      # circular nature of the next/prev list.
      if($ideogram->{display_idx} < $ideogram->{next}{display_idx}) {
	draw_axis_break($ideogram);
      }
    }
  }

  printsvg(qq{</g>}) if $SVG_MAKE;

  #report_chromosomes();exit;

  ################################################################
  #
  # inter and intra chromosome links
  #
  # these are the raison d'etre of circos
  #
  ################################################################

  # compile positional link data
  #
  # links are stored as a hash of lists, with the hash keyed
  # by the link name and the list comprised of link positions (two or more)
  #
  # $data->{links}{param}              -> HASH of global link parameters
  # $data->{links}{dataset}{ID}{param} -> HASH of link set hashes
  # $data->{links}{dataset}{ID}{data}  -> LIST of links, each link is a list of hashes
  #                                         [link1,link2,link3,...]

  $data->{links}{param} = parse_parameters( $CONF{links}, 'link' );

  for my $linkname ( keys %{ $CONF{links}{link} } ) {
    if ( ref( $CONF{links}{link}{$linkname} ) eq 'ARRAY' ) {
      confess "multiple link data sets with name [$linkname] are ",
	"defined - this is not supported"
      }

    my @param_path = ( $CONF{links}{link}{$linkname}, $CONF{links} );
    my $link_param =
      parse_parameters( $CONF{links}{link}{$linkname}, "link", 0, "file" );
    my $dataset = {};
    $dataset->{param} = $link_param;
    $dataset->{param}{name} = $linkname;
    next
      unless !defined seek_parameter( "show", @param_path )
	|| seek_parameter( "show", @param_path );
    $dataset->{data} = read_data_file(
				      locate_file( file => $link_param->{file} ),
				      'link',
				      {
				       addset       => 1,
				       groupby      => 'id',
				       record_limit => seek_parameter( 'record_limit', @param_path )
				      }
				     );

    #sanity check - must have two or more positions for each link
    for my $datum ( @{ $dataset->{data} } ) {
      unless ( @{ $datum->{data} } > 1 ) {
	confess "link data [$linkname] has a single positional ",
	  "entry for link [$datum->{data}[0]{id}]";
      }
    }

    push @{ $data->{links}{dataset} }, $dataset;

    # apply any rules to this set of links
    for my $datum ( @{ $dataset->{data} || [] } ) {
      for my $rule ( 
		    sort { $b->{importance} <=> $a->{importance} }
		    make_list( $CONF{links}{link}{$linkname}{rules}{rule} ) 
		   ) {
	delete $rule->{restart};
      }

    RULES:
      for my $rule ( 
		    sort { $b->{importance} <=> $a->{importance} }
		    make_list( $CONF{links}{link}{$linkname}{rules}{rule} ) 
		   ) {
	my $condition = $rule->{condition};
	my $flow =
	  seek_parameter( "flow", $rule,
			  $CONF{links}{link}{$linkname}{rules} );

	my $use =
	  seek_parameter( "use", $rule,
			  $CONF{links}{link}{$linkname}{rules} );

	next unless !defined $use || $use;

	my $pass =
	  test_rule( $datum, $condition,
		     [ $datum, $datum->{data}, @param_path ] );

	if ($pass) {
	  my $ruleparam = parse_parameters( $rule, "link", 1 );

	  for my $rulekey ( keys %$ruleparam ) {

	    #printinfo("rule",$rulekey);
	    my ( $rulekey_root, $rulekey_number ) =
	      $rulekey =~ /(.+?)(\d*)$/;

	    #printinfo("rulekey",$rulekey_root,$rulekey_number);
	    my $value = $ruleparam->{$rulekey};
	    if ( $value =~ /^eval\(\s*(.*)\s*\)\s*$/ ) {
	      $value =
		eval_expression( $datum, $1,
				 [ $datum, $datum->{data}, @param_path ] );
	    }

	    if ( 
		!defined $rule->{overwrite} || $rule->{overwrite} 
	       ) {
	      if ($rulekey_number) {
		$datum->{data}[ $rulekey_number - 1 ]{param}
		  {
		    $rulekey_root} = $value;
	      } else {
		$datum->{param}{$rulekey} = $value;
	      }
	    } else {
	      if ($rulekey_number) {
		$datum->{data}[ $rulekey_number - 1 ]{param}
		  {
		    $rulekey_root} = $value
		      if !
			exists $datum->{data}
			  [ $rulekey_number - 1 ]{param}{$rulekey};
	      } else {
		$datum->{param}{$rulekey} = $value
		  if !exists $datum->{param}{$rulekey};
	      }
	    }
	  }
	}

	if ($pass) {
	  if ( $flow eq "restart" && !$rule->{restart} ) {
	    $rule->{restart} = 1;
	    goto RULES;
	  }

	  last unless $flow eq "continue";
	}
      }
    }
  }

  register_z_levels( $data->{links} );

  my $links;
  my $dataset;

  for my $targetz ( @{ $data->{links}{param}{zlist} } ) {
    for my $linkset ( make_list( $data->{links}{dataset} ) ) {
      printsvg(qq{<g id="$linkset->{param}{name}">}) if $SVG_MAKE;
      my @param_path = ( $linkset, $data->{links} );
      next
	unless !defined seek_parameter( "show", @param_path )
	  || seek_parameter( "show", @param_path );
      next if seek_parameter( "hide", @param_path );

    LINK:

      # 
      # the link structure is a collection of all coordinates
      # (at least two!) that are associated together in the data
      # file by a common ID.
      # 
      for my $link ( @{ $linkset->{data} } ) {

	my @link_param_path = ( $link, @param_path );
	next
	  unless !defined seek_parameter( "show", $link )
	    || seek_parameter( "show", $link );
	next if seek_parameter( "hide", $link );

	# 
	# get the links' z depth and draw the link only if its
	# z depth is the same as the target depth, over which
	# we're iterating
	# 
	# only attempt to draw this link if all coordinates
	# are on ideogram regions that have been drawn
	# 
	my $fail;
	for my $point ( @{ $link->{data} } ) {
	  next LINK
	    if !$KARYOTYPE->{ $point->{data}{chr} }{chr}{display};
	  next LINK
	    unless $KARYOTYPE->{ $point->{data}{chr} }{chr}{display_region}{accept} ge $point->{data}{set};
	}

	my $linkradius =
	  unit_parse( seek_parameter( "radius", @link_param_path ) ) +
	    unit_parse( seek_parameter( "offset", @link_param_path ) );

	for my $i ( 1 .. @{ $link->{data} } - 1 ) {
	  my @i_link_param_path = (
				   $link,
				   $link->{data}[$i],
				   $link->{data}[ $i - 1 ], @param_path
				  );
	  my $linkz = seek_parameter( "z", @i_link_param_path );
	  next unless ($linkz == $targetz) || (! $linkz && ! $targetz);

	  my $perturb =
	    seek_parameter( "perturb", @i_link_param_path );

	  my $ideogram1 = get_ideogram_by_idx(
					      get_ideogram_idx(
							       $link->{data}[ $i - 1 ]{data}{set}->min,
							       $link->{data}[ $i - 1 ]{data}{chr}
							      )
					     );

	  my $ideogram2 = get_ideogram_by_idx(
					      get_ideogram_idx(
							       $link->{data}[$i]{data}{set}->min,
							       $link->{data}[$i]{data}{chr}
							      )
					     );

	  my ( $radius1, $radius2 );
	  if ( seek_parameter( "radius1", @i_link_param_path ) ) {
	    $radius1 =
	      unit_parse(
			 seek_parameter( "radius1", @i_link_param_path ),
			 $ideogram1 ) +
			   unit_parse(
				      seek_parameter( "offset", @link_param_path ),
				      $ideogram1 );
	  } else {
	    $radius1 = unit_parse(
				  seek_parameter(
						 "radius",
						 [ $link->{data}[ $i - 1 ], @link_param_path ]
						),
				  $ideogram1
				 ) +
				   unit_parse(
					      seek_parameter( "offset", @link_param_path ),
					      $ideogram1 );
	  }

	  if ( seek_parameter( "radius2", @i_link_param_path ) ) {
	    $radius2 =
	      unit_parse(
			 seek_parameter( "radius2", @i_link_param_path ),
			 $ideogram2 ) +
			   unit_parse(
				      seek_parameter( "offset", @link_param_path ),
				      $ideogram2 );
	  } else {
	    $radius2 = unit_parse(
				  seek_parameter(
						 "radius",
						 [ $link->{data}[$i], @link_param_path ]
						),
				  $ideogram2
				 ) +
				   unit_parse(
					      seek_parameter( "offset", @link_param_path ),
					      $ideogram2 );

	  }

	  if ( seek_parameter( "ribbon", @i_link_param_path ) ) {
	    my ( $start1, $end1 ) = (
				     max(
					 (
					  $link->{data}[ $i - 1 ]{param}{start}
					  || $link->{data}[ $i - 1 ]{data}{set}->min
					 ),
					 $ideogram1->{set}->min
					),
				     min(
					 (
					  $link->{data}[ $i - 1 ]{param}{end}
					  || $link->{data}[ $i - 1 ]{data}{set}->max
					 ),
					 $ideogram1->{set}->max
					)
				    );

	    my ( $start2, $end2 ) = (
				     max(
					 (
					  $link->{data}[$i]{param}{start}
					  || $link->{data}[$i]{data}{set}->min
					 ),
					 $ideogram2->{set}->min
					),
				     min(
					 (
					  $link->{data}[$i]{param}{end}
					  || $link->{data}[$i]{data}{set}->max
					 ),
					 $ideogram2->{set}->max
					)
				    );

	    if ( $link->{data}[ $i - 1 ]{data}{rev} ) {
	      ( $start1, $end1 ) = ( $end1, $start1 );
	    }

	    if ( $link->{data}[$i]{data}{rev} ) {
	      ( $start2, $end2 ) = ( $end2, $start2 );
	    }

	    if (
		seek_parameter(
			       "flat",            $link->{data}[ $i - 1 ],
			       $link->{data}[$i], @link_param_path
			      )
	       ) {
	      my %list = (
			  s1 => [
				 $start1,
				 getanglepos(
					     $start1,
					     $link->{data}[ $i - 1 ]{data}{chr}
					    )
                                ],
			  e1 => [
				 $end1,
				 getanglepos(
					     $end1,
					     $link->{data}[ $i - 1 ]{data}{chr}
					    )
                                ],
			  s2 => [
				 $start2,
				 getanglepos(
					     $start2, $link->{data}[$i]{data}{chr}
					    )
                                ],
			  e2 => [
				 $end2,
				 getanglepos(
					     $end2, $link->{data}[$i]{data}{chr}
					    )
                                ]
			 );

	      my @ends =
		sort { $list{$a}[1] <=> $list{$b}[1] } keys %list;

	      my $ends = join( $EMPTY_STR, @ends );

	      if ( $ends =~ /s1e2|s2e1|e1s2|e2s1/ ) {
		( $start1, $end1, $start2, $end2 ) =
		  ( $start1, $end1, $end2, $start2 );
	      }
	    }

	    if (
		seek_parameter(
			       "twist",           $link->{data}[ $i - 1 ],
			       $link->{data}[$i], @link_param_path
			      )
	       ) {
	      my %list = (
			  s1 => [
				 $start1,
				 getanglepos(
					     $start1,
					     $link->{data}[ $i - 1 ]{data}{chr}
					    )
                                ],
			  e1 => [
				 $end1,
				 getanglepos(
					     $end1,
					     $link->{data}[ $i - 1 ]{data}{chr}
					    )
                                ],
			  s2 => [
				 $start2,
				 getanglepos(
					     $start2, $link->{data}[$i]{data}{chr}
					    )
                                ],
			  e2 => [
				 $end2,
				 getanglepos(
					     $end2, $link->{data}[$i]{data}{chr}
					    )
                                ]
			 );
	      my @ends =
		sort { $list{$a}[1] <=> $list{$b}[1] } keys %list;
	      my $ends = join( $EMPTY_STR, @ends );
	      if ( $ends !~ /s1e2|s2e1|e1s2|e2s1/ ) {
		( $start1, $end1, $start2, $end2 ) =
		  ( $start1, $end1, $end2, $start2 );
	      }
	    }
	    #printdumper($link->{data});
	    my $url = seek_parameter("url",@i_link_param_path);
	    $url = format_url(url=>$url,param_path=>[@i_link_param_path,
						    {
						     start1=>$start1,
						     start2=>$start2,
						     end1=>$end1,
						     end2=>$end2,
						     size1=>$end1-$start1,
						     size2=>$end2-$start2,
						     start=>round(($start1+$end1)/2),
						     end=>round(($start2+$end2)/2)}]);;
	    #printinfo("ribbon",$url);
	    ribbon(
		   mapoptions => {url=> $url},
		   image     => $IM,
		   start1    => $start1,
		   end1      => $end1,
		   chr1      => $link->{data}[ $i - 1 ]{data}{chr},
		   start2    => $start2,
		   end2      => $end2,
		   chr2      => $link->{data}[$i]{data}{chr},
		   radius1   => $radius1,
		   radius2   => $radius2,
		   edgecolor => seek_parameter(
					       "stroke_color", @i_link_param_path
					      ),
		   edgestroke => seek_parameter(
						"stroke_thickness", @i_link_param_path
					       ),
		   fillcolor =>
		   seek_parameter( "color", @i_link_param_path ),

		   bezier_radius => seek_parameter(
						   "bezier_radius", @i_link_param_path
						  ),
		   perturb_bezier_radius => seek_parameter(
							   "perturb_bezier_radius", @i_link_param_path
							  ),

		   bezier_radius_purity => seek_parameter(
							  "bezier_radius_purity", @i_link_param_path
							 ),
		   perturb_bezier_radius_purity => seek_parameter(
								  "perturb_bezier_radius_purity",
								  @i_link_param_path
								 ),

		   crest => seek_parameter( "crest", @i_link_param_path ),
		   perturb_crest => seek_parameter(
						   "perturb_crest", @i_link_param_path
						  ),
		   
		  );
	  } elsif (
		   defined 
		   seek_parameter( "bezier_radius", @i_link_param_path ) 
		  ) {
	    my @bezier_control_points = bezier_control_points(
							      pos1 => get_set_middle(
										     $link->{data}[ $i - 1 ]{data}{set}
										    ),
							      chr1 => $link->{data}[ $i - 1 ]{data}{chr},
							      pos2 =>
							      get_set_middle( $link->{data}[$i]{data}{set} ),
							      chr2    => $link->{data}[$i]{data}{chr},
							      radius1 => $radius1,
							      radius2 => $radius2,

							      bezier_radius => seek_parameter(
											      "bezier_radius", @i_link_param_path
											     ),
							      perturb_bezier_radius => seek_parameter(
												      "perturb_bezier_radius", @i_link_param_path
												     ),

							      bezier_radius_purity => seek_parameter(
												     "bezier_radius_purity", @i_link_param_path
												    ),
							      perturb_bezier_radius_purity => seek_parameter(
													     "perturb_bezier_radius_purity",
													     @i_link_param_path
													    ),

							      crest =>
							      seek_parameter( "crest", @i_link_param_path ),
							      perturb_crest => seek_parameter(
											      "perturb_crest", @i_link_param_path
											     ),
							     );

	    my @bezier_points =
	      bezier_points(@bezier_control_points);

	    printdebug( 
		       "beziercontrols",
		       int(@bezier_control_points),
		       @bezier_control_points 
		      );

	    my $svg;
	    if ( @bezier_control_points == 10 && $SVG_MAKE ) {
	      # bezier control points P0..P4
	      # P0 - start
	      # P1,P2,P3 - controls
	      # P4 - end
	      my $getu = sub {
		my ( $x1, $y1, $x2, $y2, $x3, $y3 ) = @_;
		my $u =
		  ( ( $x3 - $x1 ) * ( $x2 - $x1 ) +
		    ( $y3 - $y2 ) * ( $y2 - $y1 ) ) /
		      ( ( $y2 - $y1 )**2 + ( $x2 - $x1 )**2 );
		my $x = $x1 + $u * ( $x2 - $x1 );
		my $y = $y1 + $u * ( $y2 - $y1 );
		return ( $x, $y, $u );
	      };

	      # 
	      # intersection between line P0-P1 and
	      # perpendicular from P2
	      # 
	      my ( $x1, $y1, $u1 ) =
		$getu->( @bezier_control_points[ 0 .. 5 ] );

	      # 
	      # intersection between line P3-P4 and
	      # perpendicular from P2
	      # 
	      my ( $x2, $y2, $u2 ) = $getu->(
					     @bezier_control_points[ 6 .. 9 ],
					     @bezier_control_points[ 4, 5 ]
					    );

	      my @c1 = @bezier_control_points[ 2, 3 ];
	      my @c2 = @bezier_control_points[ 4, 5 ];
	      my @c3 = @bezier_control_points[ 6, 7 ];

	      #
	      # bug fix v0.41 use Perl's parametrization
	      # of quartic Bezier when crest is used
	      #
	      my $point_string =
		"%.1f,%.1f " x ( @bezier_points - 1 );
	      $svg = sprintf(
			     qq{<path d="M %.1f,%.1f L $point_string " style="stroke-width: %.1f; stroke: rgb(%d,%d,%d); fill: none" />},
			     ( map { @$_ } @bezier_points[ 0, 1 ] ),
			     (
			      map { @$_ }
			      @bezier_points[ 2 .. @bezier_points - 1 ]
			     ),
			     seek_parameter(
					    "thickness", @i_link_param_path
					   ),
			     rgb_color(
				       seek_parameter(
						      "color", @i_link_param_path
						     )
				      ),
                            );
	    } elsif ( @bezier_control_points == 8 && $SVG_MAKE ) {
	      my $point_string = join( $SPACE,
				       map { sprintf( "%.1f", $_ ) }
				       @bezier_control_points[ 2 ..
							       @bezier_control_points - 1 ] );
	      $svg = sprintf(
			     qq{<path d="M %.1f,%.1f C %s" style="stroke-width: %.1f; stroke: rgb(%d,%d,%d); fill: none" />},
			     @bezier_control_points[ 0, 1 ],
			     $point_string,
			     seek_parameter(
					    "thickness", @i_link_param_path
					   ),
			     rgb_color(
				       seek_parameter(
						      "color", @i_link_param_path
						     )
				      ),
                            );
	    } elsif ( @bezier_control_points == 6 && $SVG_MAKE ) {
	      $svg = sprintf(
			     qq{<path d="M %.1f,%.1f Q %.1f,%.1f %.1f,%.1f" style="stroke-width: %.1f; stroke: rgb(%d,%d,%d); fill: none" />},
			     @bezier_control_points,
			     seek_parameter(
					    "thickness", @i_link_param_path
					   ),
			     rgb_color(
				       seek_parameter(
						      "color", @i_link_param_path
						     )
				      ),
                            );
	    }

	    printsvg($svg) if $SVG_MAKE;

	    draw_bezier(
			\@bezier_points,
			seek_parameter( "thickness", @i_link_param_path ),
			seek_parameter( "color",     @i_link_param_path ),
		       ) if $PNG_MAKE;
	  } else {
	    my ( $a1, $a2 ) = (
			       getanglepos(
					   get_set_middle(
							  $link->{data}[ $i - 1 ]{data}{set}
							 ),
					   $link->{data}[ $i - 1 ]{data}{chr}
					  ),
			       getanglepos(
					   get_set_middle( $link->{data}[$i]{data}{set} ),
					   $link->{data}[$i]{data}{chr}
					  )
			      );

	    my ( $x1, $y1 ) = getxypos( $a1, $linkradius );
	    my ( $x2, $y2 ) = getxypos( $a2, $linkradius );

	    draw_line(
		      [ $x1, $y1, $x2, $y2 ],
		      seek_parameter( "thickness", @i_link_param_path ),
		      seek_parameter( "color",     @i_link_param_path )
		     );
	  }
	}
      }

      printsvg(qq{</g>}) if $SVG_MAKE;
    }
  }

  my @plots = make_list( $CONF{plots}{plot} );
  $data->{plots}{param} = parse_parameters( $CONF{plots}, "plot" );

  for my $plot ( make_list( $CONF{plots}{plot} ) ) {
    my @param_path = ( $plot, $CONF{plots} );
    my $plot_param = parse_parameters( $plot, "plot", 0, "file" );
    my $dataset = {};
    $dataset->{param} = $plot_param;
    next
      unless !defined seek_parameter( "show", @param_path )
	|| seek_parameter( "show", @param_path );

    my $type = seek_parameter( "type", @param_path );

    if ( $type eq "text" ) {
      $dataset->{data} = read_data_file(
					locate_file( file => $plot_param->{file} ),
					"text",
					{
					 addset => 0,
					 record_limit =>
					 seek_parameter( "record_limit", @param_path )
					}
				       );
    } elsif ( $type eq "highlight" ) {
      $dataset->{data} = read_data_file(
					locate_file( file => $plot_param->{file} ),
					"highlight",
					{
					 addset => 0,
					 record_limit =>
					 seek_parameter( "record_limit", @param_path )
					}
				       );
    } elsif ( $type eq "tile" ) {
      $dataset->{data} = read_data_file(
					locate_file( file => $plot_param->{file} ),
					"tile",
					{
					 addset => 0,
					 record_limit =>
					 seek_parameter( "record_limit", @param_path )
					}
				       );
    } elsif ( $type eq "connector" ) {
      $dataset->{data} = read_data_file(
					locate_file( file => $plot_param->{file} ),
					"connector",
					{
					 addset => 0,
					 record_limit =>
					 seek_parameter( "record_limit", @param_path )
					}
				       );
    } elsif ( $type eq "histogram" ) {
      $dataset->{data} = read_data_file(
					locate_file( file => $plot_param->{file} ),
					"plot",
					{
					 addset => 0,
					 sort_bin_values =>
					 seek_parameter( "sort_bin_values", @param_path ),
					 param => {
						   fill_color =>
						   seek_parameter( "fill_color", @param_path ),
						   thickness => seek_parameter( "thickness", @param_path ),
						   color     => seek_parameter( "color",     @param_path ),
						  },
					 skip_run => seek_parameter( "skip_run", @param_path ),
					 min_value_change =>
					 seek_parameter( "min_value_change", @param_path ),
					 record_limit =>
					 seek_parameter( "record_limit", @param_path )
					}
				       );
    } else {
      $dataset->{data} = read_data_file(
					locate_file( file => $plot_param->{file} ),
					"plot",
					{
					 addset   => 0,
					 skip_run => seek_parameter( "skip_run", @param_path ),
					 min_value_change =>
					 seek_parameter( "min_value_change", @param_path ),
					 record_limit =>
					 seek_parameter( "record_limit", @param_path )
					}
				       );
    }

    # 
    # sanity check - must have two or more positions for each link
    # 
    push @{ $data->{plots}{dataset} }, $dataset;

    # 
    # apply any rules to this plot
    # 
    for my $datum ( @{ $dataset->{data} } ) {
      for my $rule ( 
		    sort { $b->{importance} <=> $a->{importance} }
		    make_list( $plot->{rules}{rule} ) 
		   ) {
	my $condition = $rule->{condition};
	my $flow      = seek_parameter( "flow", $rule, $plot->{rules} );
	my $pass      = test_rule( $datum, $condition );
	if ($pass) {
	  my $ruleparam = parse_parameters( $rule, "plot", 1 );
	  for my $rulekey ( keys %$ruleparam ) {
	    my $value = $ruleparam->{$rulekey};

	    if ( $value =~ /^eval\(\s*(.*)\s*\)\s*$/ ) {
	      $value =
		eval_expression( $datum, $1,
				 [ $datum, $datum->{data}, @param_path ] );

	      #printinfo("newvalue",$value);
	    }

	    if ( $rulekey eq "value" ) {
	      if ( $type eq "text" ) {
		$datum->{data}[0]{data}{label} = $value;
	      } else {
		$datum->{data}[0]{data}{value} = $value;
	      }
	    } else {
	      if ( !defined $rule->{overwrite}
		   || $rule->{overwrite} ) {
		$datum->{param}{$rulekey} = $value;
	      } elsif ( !exists $datum->{param}{$rulekey} ) {
		$datum->{param}{$rulekey} = $value;
	      }
	    }
	  }

	  last unless $flow eq "continue";
	}
      }
    }
  }

  register_z_levels( $data->{plots} );

  my $plotid = 0;

  for my $targetz ( @{ $data->{plots}{param}{zlist} } ) {
    for my $dataset ( make_list( $data->{plots}{dataset} ) ) {

      my @param_path = ( $dataset, $CONF{plots} );
      next unless (seek_parameter( "z", @param_path ) == $targetz) || (! seek_parameter("z",@param_path) && ! $targetz);

      printsvg(qq{<g id="plot$plotid">}) if $SVG_MAKE;

      my $plot_type = seek_parameter( "type", @param_path );
      printinfo( "drawing plot type", $plot_type, "at z-depth",
		 $targetz );

      # global properties of the plot
      my $orientation = seek_parameter( "orientation", @param_path );
      my $orientation_direction = $orientation eq "in" ? -1 : 1;

      next
	unless !defined seek_parameter( "show", @param_path )
	  || seek_parameter( "show", @param_path );

      my $plot;
      my $r0 = unit_parse( seek_parameter( "r0", @param_path ) );
      my $r1 = unit_parse( seek_parameter( "r1", @param_path ) );

      my ( @tilelayers, $margin );
      if ( seek_parameter( "type", @param_path ) eq "tile" ) {

	# the margin must be in bases
	$margin = seek_parameter( "margin", @param_path );
	unit_validate( $margin, "margin", qw(u b) );
	$margin = unit_convert(
			       from    => $margin,
			       to      => "b",
			       factors => { ub => $CONF{chromosomes_units} }
			      );

	for my $ideogram (@IDEOGRAMS) {
	  $tilelayers[ $ideogram->{idx} ] =
	    [ map { { set => Set::IntSpan->new(), idx => $_ } }
	      ( 0 .. seek_parameter( "layers", @param_path ) - 1 )
	    ];
	}
      }

      my $plot_min = seek_parameter( "min", @param_path );
      my $plot_max = seek_parameter( "max", @param_path );

      #
      # get some statistics for certain plot types, so that we
      # can set default if parameters are not defined
      #
      if ( 
	  $plot_type =~ /line|histogram|heatmap/
	  && 
	  ( !defined $plot_min || !defined $plot_max ) 
	 ) {
	my @values;
	for my $datum ( @{ $dataset->{data} } ) {
	  next
	    unless !defined seek_parameter( "show", $datum )
	      || seek_parameter( "show", $datum );
	  my $data_point = $datum->{data}[0]{data};

	  # the chromosome for the point must be displayed
	  next
	    unless $KARYOTYPE->{ $data_point->{chr} }{chr}{display};

	  #
	  # the start and end positions of the point span
	  # must be within displayed region
	  #
	  next
	    unless $KARYOTYPE->{ $data_point->{chr} }{chr}{display_region}{accept}->member( $data_point->{start} );

	  next
	    unless $KARYOTYPE->{ $data_point->{chr} }{chr}{display_region}{accept}->member( $data_point->{end} );

	  push @values, $datum->{data}[0]{data}{value};
	}

	my $min   = min(@values);
	my $max   = max(@values);
	$plot_min = $min if !defined $plot_min;
	$plot_max = $max if !defined $plot_max;
      }

      if ( $plot_type =~ /text/ ) {
	# 
	# number of discrete steps in a degree
	# e.g. for each 1000px of radius, there are 17 pixels
	# per degree along circumference (e.g. 34 for 2000px
	# radius)
	# the resolution should be set to at least twice that value
	# 
	my $angular_resolution =
	  seek_parameter( "resolution", @param_path )
	    || 0.5 * 17 * $r1 / 1000;

	#
	# label link dimensions - key
	#
	#      00112223344 (link dims)
	# LABEL  --\
	#           \
	#            \--  LABEL
	#
	#
	# assign immutable label properties
	# - pixel width, height
	# - original angular position
	# - angular width at base
	#
	# also tally up the number of labels for an angular bin
	printinfo( "processing text track - this might take a ",
		   "while - use -debug to see progress"
		 );

	for my $datum ( @{ $dataset->{data} } ) {
	  next
	    unless !
	      defined seek_parameter( "show", $datum, @param_path )
		|| seek_parameter( "show", $datum, @param_path );

	  my $data_point    = $datum->{data}[0]{data};
	  my $labelfontfile = locate_file(
					  file => $CONF{fonts}{
					    seek_parameter( "label_font", $datum, @param_path )
					      || "default"
					    }
					 );

	  $data_point->{size} = unit_strip(
					   unit_validate(
							 seek_parameter( "label_size", $datum, @param_path ),
							 "plots/plot/label_size",
							 "p"
							)
					  );

	  my ( $label_width, $label_height ) = text_size(
							 fontfile => $labelfontfile,
							 size     => $data_point->{size},
							 text     => $data_point->{label}
							);

	  @{$data_point}{qw(w h)} = ( $label_width, $label_height );

	  # 
	  # radial padding is along radial direction - can
	  # be absolute (p) or relative (r, to label width)
	  # computing padding here because it depends on the
	  # label size
	  # 
	  if ( seek_parameter( "show_links", @param_path ) ) {
	    my @link_dims =
	      split( /[, ]+/,
		     seek_parameter( "link_dims", @param_path ) );

	    @link_dims = map {
	      unit_convert(
			   from => unit_validate(
						 $_, "plots/plot/link_dims", qw(r p)
						),
			   to      => "p",
			   factors => { rp => $data_point->{w} }
			  )
	    } @link_dims;

	    $data_point->{rpadding} = sum(@link_dims);
	  } else {
	    $data_point->{rpadding} = unit_convert(
						   from => unit_validate(
									 seek_parameter(
											"rpadding", $datum, @param_path
										       ),
									 "plots/plot/rpadding",
									 qw(r p)
									),
						   to      => "p",
						   factors => { rp => $data_point->{w} }
						  );
	  }

	  #
	  # original angular position, radius
	  # - inner layer radius includes padding for link lines
	  #
	  my $angle = getanglepos(
				  ( $data_point->{start} + $data_point->{end} ) / 2,
				  $data_point->{chr} );

	  my $radius = $r0;

	  @{$data_point}{qw(angle radius)} = ( $angle, $radius );

	  #
	  # angular height, compensated for height
	  # reduction, at the start (inner) and end (outer)
	  # of the label; ah_outer < ah_inner because radius
	  # of the former is larger
	  #
	  $data_point->{ah_inner} =
	    $RAD2DEG * $data_point->{h} / $data_point->{radius};

	  $data_point->{ah_outer} =
	    $RAD2DEG *
	      $data_point->{h} /
		( $data_point->{radius} + $data_point->{w} );

	  #
	  # angular height set, in units of
	  # 1/angular_resolution, at the foot (inner) and
	  # top (outer) of the label
	  #
	  $data_point->{aset_inner} = span_from_pair(
						     map { angle_to_span( $_, $angular_resolution ) } (
												       $data_point->{angle} - $data_point->{ah_inner} / 2,
												       $data_point->{angle} + $data_point->{ah_inner} / 2
												      )
						    );

	  $data_point->{aset_outer} = span_from_pair(
						     map { angle_to_span( $_, $angular_resolution ) } (
												       $data_point->{angle} - $data_point->{ah_outer} / 2,
												       $data_point->{angle} + $data_point->{ah_outer} / 2
												      )
						    );

	  printdebug(
		     sprintf(
			     "label %s size %.1f w %d h %d rp %.1f a %.2f r %d ah %.3f %.3f asi %.2f %.2f aso %.2f %.2f",
			     @{$data_point}{
			       qw(label size w h rpadding angle radius ah_inner ah_outer)
			     },
			     (
			      map { $_ / $angular_resolution } (
								$data_point->{aset_inner}->min,
								$data_point->{aset_inner}->max
							       )
			     ),
			     (
			      map { $_ / $angular_resolution } (
								$data_point->{aset_outer}->min,
								$data_point->{aset_outer}->max
							       )
			     )
			    )
                    );
	}

	my @colors           = qw(black red orange green blue purple);
	my $label_not_placed = 0;
	my $label_placed     = 0;
	my $all_label_placed = 0;
	my %all_label_placed_iters;

	#
	# keep track of height values for each angular
	# position (sampled at $resolution)
	#
	my @stackheight =
	  map { Set::IntSpan->new() }
	    ( 0 .. 720 * $angular_resolution );

	#
	# angular coverage of previous labels to avoid placing
	# new labels which overlap
	#
	my $layer = 0;

	#
	# On the first iteration (seek_min_height=1), this is
	# the variable that holds the lowest maxheight found.
	# On subsequent iteration, labels that are near this
	# height are placed.
	#
	my $seek_min_height = 1;
	my $global_min_height;

	my $t;

	# TODO
	# Sort labels by size then anglular position
	#
	my @label_data = sort {
	  (
	   substr( $b->{data}[0]{param}{label_size}, 0, -1 ) <=>
	   substr( $a->{data}[0]{param}{label_size}, 0, -1 ) )
	    || ( $a->{data}[0]{data}{angle} <=> $b->{data}[0]{data}{angle} )
	  } @{ $dataset->{data} };
	
	do {
	  $label_placed = 0;

	TEXTDATUM:
	  for my $datum (@label_data) {
	    next
	      unless !
		defined seek_parameter( "show", $datum,
					@param_path )
		  || seek_parameter( "show", $datum, @param_path );
	    my $data_point = $datum->{data}[0]{data};

	    #
	    # don't process this point if it has already
	    # been assigned to a layer
	    #
	    next if defined $data_point->{layer};
	    if ( $data_point->{skip} ) {
	      delete $data_point->{skip};
	      next TEXTDATUM;
	    }

	    #
	    # determine maximum height of labels in this
	    # labels' angular span
	    #
	    my @range;
	    if ( !seek_parameter( "label_snuggle", @param_path ) ) {
	      @range = (0);
	    } else {
	      my $maxd = unit_convert(
				      from => unit_validate(
							    seek_parameter(
									   "max_snuggle_distance", @param_path
									  ),
							    "plots/plot/max_snuggle_distance",
							    qw(r p)
							   ),
				      to      => "p",
				      factors => { rp => $data_point->{h} }
				     );
	      my $range_center =
		0;		#max(-$maxd,-$data_point->{h}/2);
	      my $k =
		seek_parameter( "snuggle_sampling", @param_path )
		  || 1;
	      @range = sort {
		abs( $a - $range_center ) <=>
		  abs( $b - $range_center )
		}
		map {
		  (
		   $range_center - $_ * $k,
		   $range_center + $_ * $k
		  )
		} ( 0 .. $maxd / $k );
	      @range = (0) if !@range;
	    }

	    my (
		$aset_inner_best, $label_min_height,
		$angle_new,       $pix_shift_best
	       );

	  ASHIFT:
	    for my $pix_shift (@range) {
	      my $angle_new =
		$data_point->{angle} +
		  $RAD2DEG * $pix_shift / $data_point->{radius};
	      my $label_curr_height;
	      my $ah_inner;
	      for my $iter ( 0 .. 1 ) {
		my $h =
		  defined $label_curr_height
		    ? $label_curr_height
		      : $stackheight[
				     ( $angle_new + 45 -
				       $CONF{image}{angle_offset} ) *
				     $angular_resolution
				    ]->max();
		$ah_inner =
		  $RAD2DEG *
		    $data_point->{h} /
		      ( $data_point->{radius} + $h );

		my @elems = (
			     int(
				 (
				  $angle_new -
				  $ah_inner / 2 + 45 -
				  $CONF{image}{angle_offset}
				 ) * $angular_resolution
				) ... int(
					  (
					   $angle_new +
					   $ah_inner / 2 + 45 -
					   $CONF{image}{angle_offset}
					  ) * $angular_resolution
					 )
			    );

		$label_curr_height =
		  max( map { $_->max } @stackheight[@elems] )
		    || 0;
	      }

	      if ( 
		  $data_point->{radius} 
		  + $label_curr_height
		  + $data_point->{w} 
		  > $r1 
		 ) {
		next ASHIFT;
	      }

	      my $d    = $label_curr_height - $global_min_height;
	      my $flag = $DASH;
	      my $pass = 0;

	      if ( !$seek_min_height ) {
		my $tol = 0;
		if (
		    seek_parameter(
				   "snuggle_tolerance", @param_path
				  )
		   ) {
		  $tol = unit_convert(
				      from => unit_validate(
							    seek_parameter(
									   "snuggle_tolerance", @param_path
									  ),
							    "plots/plot/snuggle_tolerance",
							    qw(r p)
							   ),
				      to      => "p",
				      factors => { rp => $data_point->{w} }
				     );
		}

		if ( !defined $label_min_height ) {
		  $pass = 1 if $d <= $tol;
		} else {
		  if ( $d < 0 ) {
		    #$pass = 1;
		    ;		# change condition here? - ky
		  } elsif ( $d <= $tol ) {
		    $pass = 1
		      if abs($pix_shift) <
			abs($pix_shift_best);
		  }
		}
	      } else {
                                #
                                # we're looking for the min height for
                                # this label
                                #
		if ( !defined $label_min_height ) {
		  $pass = 1;
		} else {
		  $pass = 1
		    if $label_curr_height < $label_min_height;
		}
	      }

	      if ($pass) {
		$label_min_height = $label_curr_height;
		$data_point->{label_min_height} =
		  $label_min_height;

		$flag = $PLUS_SIGN;

		if ( !$seek_min_height ) {
		  $data_point->{angle_new} = $angle_new;
		  $aset_inner_best = span_from_pair(
						    map {
						      angle_to_span( $_,
								     $angular_resolution )
						    } (
						       $angle_new - $ah_inner / 2,
						       $angle_new + $ah_inner / 2
						      )
						   );

		  $pix_shift_best = $pix_shift;
		  $flag           = "*";
		}
	      }

	      printdebug(
			 "layer",
			 $layer,
			 "snuggle",
			 $seek_min_height ? "seek" : "mtch",
			 $flag,
			 $data_point->{label},
			 sprintf( "%.1f", $pix_shift ),
			 "d",
			 $d,
			 "label_min_height",
			 $label_min_height,
			 "global_min_height",
			 $global_min_height
			);
	    }

	    #
	    # store the lowest maxheight seen
	    #
	    if ($seek_min_height) {
	      my $d = $label_min_height - $global_min_height;

	      if ( $d < 0 || !defined $global_min_height ) {
		$global_min_height = $label_min_height;
	      } elsif ( $d > 0 ) {
		$data_point->{skip} = 1;
	      }
	      next TEXTDATUM;
	    } else {
	      #
	      # this label was not placed on this
	      # iteration - go to next label
	      #
	      next TEXTDATUM if !defined $data_point->{angle_new};
	    }

	    #
	    # if we got this far, at least one label was placed,
	    # therefore reset the unplaced counter
	    #
	    $label_not_placed = 0;

	    #
	    # make sure that the label's link does not
	    # interfere with previously placed labels
	    #
	    if (
		!$seek_min_height
		&& seek_parameter( "show_links", @param_path )
		&& seek_parameter(
				  "snuggle_link_overlap_test", @param_path
				 )
	       ) {
	      my ( $angle_from, $angle_to ) =
		sort { $a <=> $b }
		  @{$data_point}{qw(angle angle_new)};

	      my $r = $data_point->{radius} + $label_min_height;

	      my $linkset = Set::IntSpan->new(
					      sprintf( "%d-%d",
						       $label_min_height,
						       $label_min_height +
						       $data_point->{rpadding} )
					     );

	      my $tol = 0;

	      if (
		  seek_parameter(
				 "snuggle_link_overlap_tolerance",
				 @param_path
                                )
		 ) {
		$tol = unit_convert(
                                    from => unit_validate(
							  seek_parameter(
									 "snuggle_link_overlap_tolerance",
									 @param_path
									),
							  "plots/plot/snuggle_link_overlap_tolerance",
							  qw(r p)
							 ),
                                    to      => "p",
                                    factors => { rp => $data_point->{w} }
				   );
	      }

	      my $j = 0;
	      for my $i (
			 int(
			     (
			      $angle_from + 45 -
			      $CONF{image}{angle_offset}
			     ) * $angular_resolution
			    )
			 ... 
			 int(
			     (
			      $angle_to + 45 -
			      $CONF{image}{angle_offset}
			     ) * $angular_resolution
			    )
			) {
		my $collision =
		  $stackheight[$i]->intersect($linkset)
		    ->cardinality - 1;

		next
		  if seek_parameter( "snuggle_sampling",
				     @param_path )
		    and
		      $j++ % seek_parameter( "snuggle_sampling",
					     @param_path );

		if ( $collision > $tol ) {
		  delete $data_point->{angle_new};
		  $data_point->{skip} = 1;
		  next TEXTDATUM;
		}
	      }
	    }

	    my $a_padding = unit_convert(
					 from => unit_validate(
							       seek_parameter(
									      "padding", $datum, @param_path
									     ),
							       "plots/plot/padding",
							       qw(r p)
							      ),
					 to      => "p",
					 factors => { rp => $data_point->{h} }
					);

	    my $padding =
	      $angular_resolution *
		$RAD2DEG *
		  $a_padding /
		    ( $label_min_height + $data_point->{radius} );

	    my $aset_padded = $aset_inner_best->trim( -$padding );
	    $data_point->{radius_shift} = $label_min_height;

	    printdebug(
		       "layer", $layer, $PLUS_SIGN,
		       $data_point->{label},
		       "mh",
		       $label_min_height,
		       "a",
		       sprintf( "%.3f", $data_point->{angle} ),
		       "an",
		       sprintf( "%.3f", $data_point->{angle_new} ),
		       "as",
		       sprintf( "%.3f",
                                $data_point->{angle_new} -
				$data_point->{angle} ),
		       "rs",
		       $data_point->{radius_shift}
		      );

	    $data_point->{layer} = $layer;
	    $label_placed++;
	    $all_label_placed++;

	    my $ah_outer =
	      $RAD2DEG *
		$data_point->{h} /
		  ( $data_point->{radius} +
		    $data_point->{radius_shift} +
		    $data_point->{w} );

	    my $ah_set_outer = span_from_pair(
					      map { angle_to_span( $_, $angular_resolution ) } (
												$data_point->{angle_new} - $ah_outer / 2,
												$data_point->{angle_new} + $ah_outer / 2
											       )
					     );

	    $ah_set_outer = $ah_set_outer->trim( -$padding );

	    printdebug(
		       "labelplaced",
		       $data_point->{label},
		       $data_point->{radius} + $data_point->{radius_shift},
		       $data_point->{radius} +
		       $data_point->{radius_shift} +
		       $data_point->{w} +
		       $data_point->{rpadding}
		      );

	    for my $a ( $ah_set_outer->elements ) {
	      my $height =
		$data_point->{radius_shift} +
		  $data_point->{w} +
		    $data_point->{rpadding};

	      my $i = $a + 45 * $angular_resolution;

	      $stackheight[$i]->U(
				  Set::IntSpan->new(
						    sprintf( "%d-%d",
							     $data_point->{radius_shift} +
							     $data_point->{rpadding},
							     $data_point->{radius_shift} +
							     $data_point->{w} +
							     $data_point->{rpadding} )
						   )
				 );
	    }
	  }			# TEXTDATUM

	  printdebug(
		     "iterationsummary", "seekmin",
		     $seek_min_height,   "global_min_height",
		     $global_min_height, "placed",
		     $label_placed,      "all",
		     $all_label_placed
                    );

	  #
	  # refine angular position within this layer for
	  # adjacent labels
	  #
	  my $refined;
	  do {
	    $refined = 0;
	    my $data_point_prev;
	    for my $datum (@label_data) {
	      next
		unless seek_parameter( "snuggle_refine",
				       @param_path );
	      next
		unless !
		  defined seek_parameter( "show", $datum,
					  @param_path )
		    || seek_parameter( "show", $datum,
				       @param_path );
	      my $data_point = $datum->{data}[0]{data};

	      next
		unless defined $data_point->{layer}
		  && $data_point->{layer} == $layer;

	      if ($data_point_prev) {
		my $tol = unit_convert(
				       from => unit_validate(
							     seek_parameter(
									    "snuggle_tolerance", @param_path
									   ),
							     "plots/plot/snuggle_tolerance",
							     qw(r p)
							    ),
				       to      => "p",
				       factors => { rp => $data_point->{w} }
				      );

		if (
		    $data_point->{angle_new} <
		    $data_point_prev->{angle_new}
		    && abs(
			   $data_point->{radius_shift} -
			   $data_point_prev->{radius_shift}
			  ) < 15
		   ) {
		  $refined = 1;
		  printdebug(
			     "refined",
			     $data_point->{label},
			     $data_point->{angle_new},
			     $data_point_prev->{label},
			     $data_point_prev->{angle_new}
			    );

		  (
		   $data_point->{angle_new},
		   $data_point_prev->{angle_new}
		  ) = (
		       $data_point_prev->{angle_new},
		       $data_point->{angle_new}
		      );

		  printdebug(
			     "refined",
			     $data_point->{label},
			     $data_point->{angle_new},
			     $data_point_prev->{label},
			     $data_point_prev->{angle_new}
			    );

		  for my $dp ( $data_point, $data_point_prev ) {
		    my $ah_outer =
		      $RAD2DEG *
			$dp->{h} /
			  ( $dp->{radius} +
			    $dp->{radius_shift} +
			    $data_point->{w} );
		    my $ah_set_outer = span_from_pair(
						      map {
							angle_to_span( $_,
								       $angular_resolution )
						      } (
							 $dp->{angle_new} -
							 $ah_outer / 2,
							 $dp->{angle_new} + $ah_outer / 2
							)
						     );

		    my $a_padding = unit_convert(
						 from => unit_validate(
								       seek_parameter(
										      "padding", $datum,
										      @param_path
										     ),
								       "plots/plot/padding",
								       qw(r p)
								      ),
						 to      => "p",
						 factors => { rp => $dp->{h} }
						);

		    my $padding =
		      $angular_resolution *
			$RAD2DEG *
			  $a_padding /
			    ( $dp->{radius} +
			      $dp->{radius_shfit} );

		    $ah_set_outer =
		      $ah_set_outer->trim( -$padding );

		    for my $a ( $ah_set_outer->elements ) {
		      my $height =
			$dp->{radius_shift} +
			  $dp->{w} +
			    $dp->{rpadding};
		      my $i =
			$a + 45 * $angular_resolution;
		      $stackheight[$i]->U(
					  Set::IntSpan->new(
							    sprintf( "%d-%d",
								     $dp->{radius_shift} +
								     $dp->{rpadding},
								     $dp->{radius_shift} +
								     $dp->{w} +
								     $dp->{rpadding} )
							   )
					 );
		    }
		  }
		  last;
		}
	      }
	      $data_point_prev = $data_point;
	    }
	  } while ($refined);

	  if ($seek_min_height) {
	    printdebug( "toggle", 0 );
	    $seek_min_height = 0;
	  } else {
	    $seek_min_height = 1;
	    if ( !$label_placed ) {
	      printdebug( "toggle", 1 );
	      $label_not_placed++;
	      $layer++;
	      $global_min_height = undef;
	    } else {
	      printdebug( "toggle", 2 );
	      $label_not_placed = 0;
	    }

	    if ( seek_parameter( "layers", @param_path )
		 && $layer >=
		 seek_parameter( "layers", @param_path ) ) {
	      printdebug( "toggle", 3 );
	      $label_placed     = 0;
	      $label_not_placed = 2;
	    }

	    if ( $all_label_placed_iters{$all_label_placed}++ > 20 ) {
	      printdebug( "toggle", 4 );
	      $label_placed     = 0;
	      $label_not_placed = 2;
	    }
	  }

	  printdebug(
		     "loopsummary",      "seekmin",
		     $seek_min_height,   "global_min_height",
		     $global_min_height, "label_placed",
		     $label_placed,      "label_not_placed",
		     $label_not_placed,  "all",
		     $all_label_placed
                    );
	} while ( $label_placed || $label_not_placed < 2 ) # TEXT LOOP
      }

      if ( $plot_max < $plot_min ) {
	confess "error - plot min value is larger than ",
	  "max [$plot_min,$plot_max]";
      }

      # last point plotted, by chr
      my $prevpoint;

      my %ideograms_with_data;
      for my $datum ( @{ $dataset->{data} } ) {
	my $i = get_ideogram_idx(
				 $datum->{data}[0]{data}{start},
				 $datum->{data}[0]{data}{chr}
				);
	$ideograms_with_data{$i}++ if defined $i;
      }

      my @ideograms_with_axis;
      if ( seek_parameter( "background_dataonly", @param_path ) ) {
	@ideograms_with_axis =
	  map { $IDEOGRAMS[$_] } keys %ideograms_with_data;
      } else {
	@ideograms_with_axis = @IDEOGRAMS;
      }

      printsvg(qq{<g id="plot$plotid-axis">}) if $SVG_MAKE;

      for my $ideogram (@ideograms_with_axis) {
	$r0 =
	  unit_parse( seek_parameter( "r0", @param_path ), $ideogram );
	$r1 =
	  unit_parse( seek_parameter( "r1", @param_path ), $ideogram );
	my ( $start, $end ) =
	  ( $ideogram->{set}->min, $ideogram->{set}->max );

	if ( seek_parameter( "background", @param_path ) ) {
	  slice(
		image       => $IM,
		start       => $ideogram->{set}->min,
		end         => $ideogram->{set}->max,
		chr         => $ideogram->{chr},
		radius_from => $r0,
		radius_to   => $r1,
		fillcolor =>
		seek_parameter( "background_color", @param_path ),
		edgecolor => seek_parameter(
					    "background_stroke_color", @param_path
					   ),
		edgestroke => 0,
		mapoptions => {
			       object_type   => "trackbackground",
			       object_label  => $plot_type,
			       object_parent => $ideogram->{chr},
			       object_data   => {
						 start => $ideogram->{set}->min,
						 end   => $ideogram->{set}->max
						},
			      },
	       );
	}

	if ( seek_parameter( "axis", @param_path ) ) {
	  for (
	       my $y =
	       nearest( seek_parameter( "axis_spacing", @param_path ),
			$plot_min ) ;
	       $y <= $plot_max ;
	       $y += seek_parameter( "axis_spacing", @param_path )
	      ) {
	    next if $y < $plot_min;
	    my $radius =
	      $r0 +
		abs( $r1 - $r0 ) *
		  ( $y - $plot_min ) /
		    ( $plot_max - $plot_min )
		      if $plot_max -
			$plot_min;

	    slice(
		  image       => $IM,
		  start       => $ideogram->{set}->min,
		  end         => $ideogram->{set}->max,
		  chr         => $ideogram->{chr},
		  radius_from => $radius,
		  radius_to   => $radius,
		  edgecolor =>
		  seek_parameter( "axis_color", @param_path ),
		  edgestroke =>
		  seek_parameter( "axis_thickness", @param_path ),
		  mapoptions => {
				 object_type   => "trackaxis",
				 object_label  => $plot_type,
				 object_parent => $ideogram->{chr},
				 object_data   => {
						   start => $ideogram->{set}->min,
						   end   => $ideogram->{set}->max,
						  },
				},
		 );
	  }
	}

	if ( seek_parameter( "background", @param_path ) ) {
	  slice(
		image       => $IM,
		start       => $ideogram->{set}->min,
		end         => $ideogram->{set}->max,
		chr         => $ideogram->{chr},
		radius_from => $r0,
		radius_to   => $r1,

		#fillcolor=>seek_parameter("background_color",@param_path),
		edgecolor => seek_parameter(
					    "background_stroke_color", @param_path
					   ),
		edgestroke => seek_parameter(
					     "background_stroke_thickness", @param_path
					    ),
	       );
	}
      }

      printsvg(qq{</g>}) if $SVG_MAKE;

      my ( $data_point_prev, $datum_prev, $data_point_next, $datum_next );

      my $sort_funcs = {
			text =>
			sub { $b->{data}[0]{data}{w} <=> $a->{data}[0]{data}{w} },
			default => sub {
			  ( $b->{data}[0]{param}{z} <=> $a->{data}[0]{param}{z} )
			    || ( $a->{data}[0]{data}{chr} cmp $b->{data}[0]{data}{chr}
				 || $a->{data}[0]{data}{start} <=> $b->{data}[0]{data}{start} );
			},
			heatmap => sub {
			  $b->{data}[0]{data}{end} -
			    $b->{data}[0]{data}{start} <=> $a->{data}[0]{data}{end} -
			      $a->{data}[0]{data}{start};
			},
		       };

      my $f = $sort_funcs->{$plot_type} || $sort_funcs->{default};
      my @sorted_data = grep( 
			     (
			      !defined seek_parameter( "show", $_ )
			      || 
			      seek_parameter( "show", $_ )
			     )
			     && $KARYOTYPE->{ $_->{data}[0]{data}{chr} }{chr}{display},
			     sort $f @{ $dataset->{data} } 
			    );

      for my $datum_idx ( 0 .. @sorted_data - 1 ) {

	my $datum = $sorted_data[$datum_idx];

	my $data_point = $datum->{data}[0]{data};

	# 
	# the point must have show flag set, or not defined - already
	# checked in the construction of @sorted_data next unless !
	# defined seek_parameter("show",$datum) ||
	# seek_parameter("show",$datum);
	# 
	# the chromosome for the point must be displayed checked in
	# construction of @sorted_data next unless
	# $KARYOTYPE->{$data_point->{chr}}{chr}{display};
	# 
	# the data span must intersect a displayed region
	# 
	my $data_point_set;
	if ( $plot_type eq "connector" ) {
	  # nothing to be done for connectors
	  ;
	} else {
	  $data_point_set = Set::IntSpan->new(
					      sprintf( "%d-%d",
						       $data_point->{start}, $data_point->{end} )
					     );

	  $data_point_set =
	    $data_point_set->intersect(
				       $KARYOTYPE->{ $data_point->{chr} }{chr}{display_region}{accept} );
	  
	  $data_point->{start} = $data_point_set->min;
	  $data_point->{end}   = $data_point_set->max;
	}

	#
	# the span of the data point must fall on the same ideogram
	#
	my ( $i_start, $i_end ) = (
				   get_ideogram_idx(
						    $data_point->{start}, $data_point->{chr}
						   ),
				   get_ideogram_idx( $data_point->{end}, $data_point->{chr} )
				  );

	next
	  unless defined $i_start
	    && defined $i_end
	      && $i_start == $i_end;

	my $ideogram_idx = $i_start;
	$data_point->{ideogram_idx} = $i_start;

	if ( $plot_type ne "connector" ) {
	  next
	    unless get_ideogram_by_idx($ideogram_idx)->{set}
	      ->intersect($data_point_set)->cardinality;
	} else {
	  next
	    unless get_ideogram_by_idx($ideogram_idx)->{set}
	      ->member( $data_point->{start} )
		&& get_ideogram_by_idx($ideogram_idx)->{set}
		  ->member( $data_point->{end} );
	}

	if ( $datum_idx < @sorted_data ) {
	  $datum_next      = $sorted_data[ $datum_idx + 1 ];
	  $data_point_next = $datum_next->{data}[0]{data};
	  $data_point_next->{ideogram_idx} =
	    get_ideogram_idx( $data_point_next->{start},
			      $data_point_next->{chr} );
	}

	if ( $plot_type eq "connector" ) {
	  $r0 = unit_parse(
			   seek_parameter( "r0", @param_path ),
			   get_ideogram_by_idx($i_start)
			  );

	  $r1 = unit_parse(
			   seek_parameter( "r1", @param_path ),
			   get_ideogram_by_idx($i_start)
			  );

	  my $rd     = abs( $r0 - $r1 );
	  my $angle0 = getanglepos(
				   ( $data_point->{start}, $data_point->{chr} ) );
	  my $angle1 =
	    getanglepos( ( $data_point->{end}, $data_point->{chr} ) );
	  my @dims = split( $COMMA,
			    seek_parameter( "connector_dims", @param_path ) 
			  );

	  draw_line(
		    [
		     getxypos( $angle0, $r0 + $dims[0] * $rd ),
		     getxypos(
			      $angle0, $r0 + ( $dims[0] + $dims[1] ) * $rd
			     )
		    ],
		    seek_parameter( "thickness", @param_path ),
		    seek_parameter( "color",     @param_path ),
		   );

	  if ( $angle1 > $angle0 ) {
	    my $adiff = $angle1 - $angle0;
	    my $ainit = $angle0;
	    my $acurr = $ainit;
	    my $rinit = $r0 + ( $dims[0] + $dims[1] ) * $rd;
	    my $rfinal =
	      $r0 + ( $dims[0] + $dims[1] + $dims[2] ) * $rd;
	    my $rdiff    = abs( $rfinal - $rinit );
	    my $progress = 0;

	    while ( $acurr + $CONF{anglestep} <= $angle1 ) {
	      draw_line(
			[
			 getxypos(
				  $acurr,
				  $rinit +
				  $rdiff * ( $acurr - $ainit ) / $adiff
				 ),
			 getxypos(
				  $acurr + $CONF{anglestep},
				  $rinit + $rdiff * (
						     $acurr + $CONF{anglestep} - $ainit
						    ) / $adiff
				 )
			],
			seek_parameter( "thickness", @param_path ),
			seek_parameter( "color",     @param_path ),
		       );
	      $acurr += $CONF{anglestep};
	    }

	    if ( $acurr < $angle1 ) {
	      draw_line(
			[
			 getxypos(
				  $acurr,
				  $rinit +
				  $rdiff * ( $acurr - $ainit ) / $adiff
				 ),
			 getxypos( $angle1, $rfinal )
			],
			seek_parameter( "thickness", @param_path ),
			seek_parameter( "color",     @param_path ),
		       );
	    }
	  } elsif ( $angle1 < $angle0 ) {
	    my $adiff = $angle1 - $angle0;
	    my $ainit = $angle0;
	    my $acurr = $ainit;
	    my $rinit = $r0 + ( $dims[0] + $dims[1] ) * $rd;
	    my $rfinal =
	      $r0 + ( $dims[0] + $dims[1] + $dims[2] ) * $rd;
	    my $rdiff    = abs( $rfinal - $rinit );
	    my $progress = 0;

	    while ( $acurr - $CONF{anglestep} >= $angle1 ) {
	      draw_line(
			[
			 getxypos(
				  $acurr,
				  $rinit +
				  $rdiff * ( $acurr - $ainit ) / $adiff
				 ),
			 getxypos(
				  $acurr - $CONF{anglestep},
				  $rinit + $rdiff * (
						     $acurr - $CONF{anglestep} - $ainit
						    ) / $adiff
				 )
			],
			seek_parameter( "thickness", @param_path ),
			seek_parameter( "color",     @param_path ),
		       );
	      $acurr -= $CONF{anglestep};
	    }

	    if ( $acurr > $angle1 ) {
	      draw_line(
			[
			 getxypos(
				  $acurr,
				  $rinit +
				  $rdiff * ( $acurr - $ainit ) / $adiff
				 ),
			 getxypos( $angle1, $rfinal )
			],
			seek_parameter( "thickness", @param_path ),
			seek_parameter( "color",     @param_path ),
		       );
	    }
	  } else {
	    my $rinit = $r0 + ( $dims[0] + $dims[1] ) * $rd;
	    my $rfinal =
	      $r0 + ( $dims[0] + $dims[1] + $dims[2] ) * $rd;
	    draw_line(
		      [
		       getxypos( $angle0, $rinit ),
		       getxypos( $angle1, $rfinal )
		      ],
		      seek_parameter( "thickness", @param_path ),
		      seek_parameter( "color",     @param_path ),
		     );
	  }

	  draw_line(
		    [
		     getxypos(
			      $angle1,
			      $r0 + ( $dims[0] + $dims[1] + $dims[2] ) * $rd
			     ),
		     ,
		     getxypos(
			      $angle1,
			      $r0 +
			      ( $dims[0] + $dims[1] + $dims[2] + $dims[3] )
			      * $rd
			     )
		    ],
		    seek_parameter( "thickness", @param_path ),
		    seek_parameter( "color",     @param_path ),
		   );
	  next;
	}

	if ( $plot_type eq "highlight" ) {
	  $r0 =
	    unit_parse( seek_parameter( "r0", $datum, @param_path ),
                        get_ideogram_by_idx($i_start) );

	  $r1 =
	    unit_parse( seek_parameter( "r1", $datum, @param_path ),
                        get_ideogram_by_idx($i_start) );

	  my $url = seek_parameter("url",$data_point,$datum,@param_path);
	  $url = format_url(url=>$url,param_path=>[$data_point,$datum,@param_path]);

	  slice(
		image       => $IM,
		start       => $data_point->{start},
		end         => $data_point->{end},
		chr         => $data_point->{chr},
		radius_from => $r0,
		radius_to   => $r1,
		edgecolor   => seek_parameter( "stroke_color", $datum, @param_path ),
		edgestroke  => seek_parameter( "stroke_thickness", $datum, @param_path),
		fillcolor   => seek_parameter( "fill_color", $datum, @param_path ),
		mapoptions  => {url=>$url},
	       );

	  next;
	}

	my $value = $data_point->{value};

	my $value_outofbounds;
	if ( defined $plot_min && $value < $plot_min ) {
	  $value             = $plot_min;
	  $value_outofbounds = 1;
	}
	if ( defined $plot_max && $value > $plot_max ) {
	  $value             = $plot_max;
	  $value_outofbounds = 1;
	}

	my $angle = getanglepos(
				( $data_point->{start} + $data_point->{end} ) / 2,
				$data_point->{chr} );

	$r0 = unit_parse(
			 seek_parameter( "r0", @param_path ),
			 get_ideogram_by_idx($i_start)
			);
	$r1 = unit_parse(
			 seek_parameter( "r1", @param_path ),
			 get_ideogram_by_idx($i_start)
			);

	my $radius;
	my $radius0;

	# value floor is the axis end closer to zero
	my $valuefloor =
	  abs($plot_min) < abs($plot_max) ? $plot_min : $plot_max;
	$valuefloor = 0 if $plot_min <= 0 && $plot_max >= 0;

	#
	# orientation refers to the direction of the y-axis for "in" -
	# the y-axis is oriented towards the center of the circle
	# (larger values appear closer to center) for "out" (default) -
	# the y-axis is oriented out of the center of the circle
	# (larger values appear further from the center)
	#
	my $rd = abs( $r1 - $r0 );
	my $dd = $plot_max - $plot_min;
	if ( $orientation eq "in" ) {
	  # radius of data point
	  $radius = $r1 - $rd * abs( $value - $plot_min ) / $dd
	    if $dd;

	  # radius of valuefloor
	  $radius0 = $r1 - $rd * ( $valuefloor - $plot_min ) / $dd
	    if $dd;
	} else {
	  # radius of data point
	  $radius = $r0 + $rd * ( $value - $plot_min ) / $dd if $dd;

	  # radius of valuefloor
	  $radius0 = $r0 + $rd * ( $valuefloor - $plot_min ) / $dd
	    if $dd;
	}

	if ( $plot_type ne "text" ) {
	  $data_point->{angle}  = $angle;
	  $data_point->{radius} = $radius;
	}

	if ( $plot_type eq "text" ) {
	  goto SKIPDATUM if !defined $data_point->{layer};
	  $data_point->{radius_new} =
	    $data_point->{radius} + $data_point->{radius_shift};
	  $data_point->{radius_new_label} =
	    $data_point->{radius_new} + $data_point->{rpadding};

	  $data_point->{angle_new} = $data_point->{angle}
	    if !defined $data_point->{angle_new};

	  my ( $ao, $ro ) = textoffset(
				       @{$data_point}{qw(angle_new radius_new_label w h)},
				       unit_strip(
						  unit_validate(
								seek_parameter(
									       "yoffset", $datum, @param_path
									      )
								|| "0p",
								"plots/plot/yoffset",
								"p"
							       )
						 )
				      );

	  my ( $x, $y ) = getxypos(
				   $data_point->{angle_new} + $ao,
				   $data_point->{radius_new_label} + $ro
				  );

	  my $labelfontfile = locate_file(
					  file => $CONF{fonts}{
					    seek_parameter( "label_font", $datum, @param_path )
					      || "default"
					    }
					 );

	  my $text_angle =
	    defined seek_parameter( "label_rotate", $datum, @param_path )
	      && !seek_parameter( "label_rotate", $datum, @param_path )
		? 0 : $DEG2RAD * textangle( $data_point->{angle_new} );
	  0&&printinfo( "drawing label",
		     $data_point->{label},
		     $datum->{data}[0]{param}{label_size} );

	  my $labeldata = {
			   font  => $labelfontfile,
			   color => seek_parameter( "color", $datum, @param_path ),
			   size  => unit_strip(
					       unit_validate(
							     seek_parameter(
									    "label_size", $datum, @param_path
									   ),
							     "plots/plot/label_size",
							     "p"
							    )
					      ),
			   radius => $data_point->{radius_new_label},
			   pangle => $data_point->{angle_new},
			   angle  => $text_angle,
			   xy     => [ $x, $y ],
			   svgxy  => [
				      getxypos(
					       $data_point->{angle_new} +
					       $ao / $CONF{svg_font_scale},
					       $data_point->{radius_new_label}
					      )
				     ],
			   svgangle => textanglesvg( $data_point->{angle_new} ),
			   text     => $data_point->{label},
			   chr      => $data_point->{chr},
			   start    => $data_point->{start},
			   end      => $data_point->{end},
			  };

	  if ( seek_parameter( "show_links", @param_path ) ) {
	    my @link_dims =
	      split( /[, ]+/,
		     seek_parameter( "link_dims", @param_path ) );
	    @link_dims = map {
	      unit_strip(
			 unit_validate(
				       $_, "plots/plot/link_dims", "p"
				      )
			)
	    } @link_dims;

	    #
	    #      00112223344 (link dims)
	    # LABEL  --\
	    #           \
	    #            \--  LABEL
	    #

	    my $link_thickness = unit_strip(
					    unit_validate(
							  seek_parameter(
									 "link_thickness", $datum, @param_path
									),
							  "plots/plot/link_thickness",
							  "p"
							 )
					   );
	    my $line_colors = seek_parameter( "link_color", $datum, @param_path )
	      || seek_parameter( "color", $datum, @param_path );

	    draw_line(
		      [
		       getxypos(
				$data_point->{angle},
				$data_point->{radius_new} + $link_dims[0]
			       ),
		       getxypos(
				$data_point->{angle},
				$data_point->{radius_new} +
				sum( @link_dims[ 0, 1 ] )
			       ),
		      ],
		      $link_thickness,
		      $line_colors
		     );

	    draw_line(
		      [
		       getxypos(
				$data_point->{angle},
				$data_point->{radius_new} +
				sum( @link_dims[ 0, 1 ] )
			       ),
		       getxypos(
				$data_point->{angle_new},
				$data_point->{radius_new} +
				sum( @link_dims[ 0, 1, 2 ] )
			       ),
		      ],
		      $link_thickness,
		      $line_colors
		     );

	    draw_line(
		      [
		       getxypos(
				$data_point->{angle_new},
				$data_point->{radius_new} +
				sum( @link_dims[ 0, 1, 2 ] )
			       ),
		       getxypos(
				$data_point->{angle_new},
				$data_point->{radius_new} +
			       sum( @link_dims[ 0, 1, 2, 3 ] )
			       ),
		       ],
		      $link_thickness,
		      $line_colors
		     );

	  }

	  my $url = seek_parameter( "url", $datum, @param_path );
	  $url = format_url(url=>$url,param_path=>[$data_point,$datum,@param_path]);
	  draw_text(
		    image => $IM,
		    %$labeldata,
		    mapoptions => { url=>$url }
		   );

	} elsif ( $plot_type eq "scatter" ) {

	  my $url = seek_parameter("url",$data_point,$datum,@param_path);
	  $url = format_url(url=>$url,param_path=>[$data_point,$datum,@param_path]);

	  my $glyph = seek_parameter( "glyph", $datum, @param_path );

	  if ( !$value_outofbounds ) {
	    if ( $glyph eq "circle" ) {
	      # the circle is a special glyph because it is not handled as a polygon, but rather
	      # with the circle (SVG) or arc (GD) function
	      if($SVG_MAKE) {
		my $svg_colors;
		if ( seek_parameter("stroke_color", $datum, @param_path ) ) {
		  $svg_colors .= sprintf( "stroke:rgb(%d,%d,%d);",
					  rgb_color( seek_parameter( "stroke_color", $datum, @param_path ) )
					);
		}
		  if (seek_parameter("fill_color", $datum, @param_path ) ) {
		    $svg_colors .= sprintf(
					   "fill:rgb(%d,%d,%d);",
					   rgb_color( seek_parameter( "fill_color", $datum, @param_path ) )
					  );
		  }
		my $svg = sprintf(
				  q{<circle cx="%.1f" cy="%.1f" r="%.1f" style="stroke-width: %.1f; %s"/>},
				  getxypos( $angle, $radius ),
				  seek_parameter( "glyph_size", $datum, @param_path ) / 2,
				  seek_parameter( "stroke_thickness", $datum, @param_path ),
				    $svg_colors,
				 );
		printsvg($svg);
	      }
	      if($PNG_MAKE) {
		if ( seek_parameter( "fill_color", $datum, @param_path ) ) {
		  $IM->filledArc(
				 getxypos( $angle, $radius ),
				 seek_parameter("glyph_size", $datum, @param_path),
				 seek_parameter("glyph_size", $datum, @param_path),
				 0, 360,
				 aa_color( seek_parameter("fill_color",$datum,@param_path), $IM, $COLORS )
				);
		}
		if ( seek_parameter( "stroke_thickness", $datum, @param_path ) ) {
		  my $thickness = seek_parameter( "stroke_thickness", $datum, @param_path );
		  my $stroke_color = seek_parameter( "stroke_color", $datum, @param_path );
		  my $color_obj;
		  if($thickness == 1 && rgb_color_opacity($stroke_color) == 1) {
		    # this is a 1-px thick line and the color has no transparency - 
		    # go ahead and antialias this line
		    $IM->setAntiAliased($COLORS->{$stroke_color});
		    $color_obj = gdAntiAliased;
		  } else {
		    $IM->setThickness($thickness) if $thickness > 1;
		    $color_obj = $COLORS->{$stroke_color};
		  }
		  $IM->arc(
			   getxypos( $angle, $radius ),
			   seek_parameter( "glyph_size", $datum, @param_path ),
			   seek_parameter( "glyph_size", $datum, @param_path ),
			   0, 360,
			   $color_obj,
			  );
		}
		if($url) {
		  my ($x,$y) = getxypos( $angle, $radius );
		  my $r = seek_parameter("glyph_size", $datum,@param_path);
		  my $xshift = $CONF{image}{image_map_xshift}||0;
		  my $yshift = $CONF{image}{image_map_xshift}||0;
		  my $xmult  = $CONF{image}{image_map_xfactor}||1;
		  my $ymult  = $CONF{image}{image_map_yfactor}||1;
		  my @coords = ($x*$xmult + $xshift , $y*$ymult + $yshift, $r*$xmult);
		  report_image_map(shape=>"circle",
				   coords=>\@coords,
				   href=>$url);
		}
	      }
	    } elsif (
		     $glyph eq "rectangle"
		     || $glyph eq "square"
		     || $glyph eq "triangle"
		     || $glyph eq "cross"
		     || $glyph =~ /ngon/
		    ) {
	      my ( $x, $y ) = getxypos( $angle, $radius );
	      my $size = seek_parameter( "glyph_size", $datum,
					 @param_path );
	      my $angle_shift =
		seek_parameter( "angle_shift", $datum,
                                @param_path );
	      my $poly = GD::Polygon->new();
	      my @pts;

	      if ( $glyph eq "rectangle" || $glyph eq "square" ) {
		@pts = (
			[ $x - $size / 2, $y - $size / 2 ],
			[ $x + $size / 2, $y - $size / 2 ],
			[ $x + $size / 2, $y + $size / 2 ],
			[ $x - $size / 2, $y + $size / 2 ]
		       );
	      } elsif ( $glyph eq "triangle" ) {
		@pts = (
			[ $x, $y - $size * sqrt(3) / 4 ],
			[
			 $x + $size / 2, $y + $size * sqrt(3) / 4
			],
			[
			 $x - $size / 2, $y + $size * sqrt(3) / 4
			]
		       );
	      } elsif ( $glyph eq "cross" ) {
		@pts = (
			[ $x,             $y - $size / 2 ],
			[ $x,             $y ],
			[ $x + $size / 2, $y ],
			[ $x,             $y ],
			[ $x,             $y + $size / 2 ],
			[ $x,             $y ],
			[ $x - $size / 2, $y ],
			[ $x,             $y ]
		       );
	      } elsif ( $glyph =~ /ngon(\d+)?/ ) {
		my $sides = $1 || 5;
		for my $side ( 0 .. $sides - 1 ) {
		  my $angle = 360 * $side / $sides;
		  push @pts, [ $x + $size/2 * cos( $angle * $DEG2RAD ),
			       $y + $size/2 * sin( $angle * $DEG2RAD ) ];
		}
	      }

	      map { $poly->addPt(@$_) } map {
		[ rotate_xy( @$_, $x, $y, $angle + $angle_shift ) ]
	      } @pts;

	      my $url = seek_parameter("url",$datum,@param_path);
	      $url = format_url(url=>$url,param_path=>[$data_point,$datum,@param_path]);
	      if($url) {
		my $xshift = $CONF{image}{image_map_xshift}||0;
		my $yshift = $CONF{image}{image_map_xshift}||0;
		my $xmult  = $CONF{image}{image_map_xfactor}||1;
		my $ymult  = $CONF{image}{image_map_yfactor}||1;
		my @coords = map { ( $_->[0]*$xmult + $xshift , $_->[1]*$ymult + $yshift ) } $poly->vertices;
		report_image_map(shape=>"poly",
				 coords=>\@coords,
				 href=>$url);
	      }
	      if ( seek_parameter( "fill_color", $datum, @param_path ) 
		   && 
		   $glyph ne "cross" ) {
		my $svg = sprintf(
				  q{<polygon points="%s" style="stroke-width: %.1f; stroke: rgb(%d,%d,%d); fill: rgb(%d,%d,%d);" />},
				  join( $SPACE,
                                        map { join( $COMMA, @$_ ) }
					$poly->vertices ),
				  seek_parameter("stroke_thickness", $datum,@param_path ),
				  rgb_color(seek_parameter("stroke_color", $datum, @param_path ) ),
				  rgb_color(seek_parameter("fill_color", $datum, @param_path  ) ),
				 );

		printsvg($svg);
		$IM->filledPolygon(
				   $poly,
				   aa_color( seek_parameter( "fill_color", $datum, @param_path ), $IM, $COLORS )
				  ) if $PNG_MAKE;
	      }

	      if (seek_parameter("stroke_thickness", $datum, @param_path ) ) {
		my $svg = sprintf(
				  q{<polygon points="%s" style="stroke-width: %.1f; stroke: rgb(%d,%d,%d); fill: none;" />},
				  join( $SPACE,
                                        map { join( $COMMA, @$_ ) }
					$poly->vertices ),
				  seek_parameter("stroke_thickness", $datum,@param_path),
				  rgb_color(seek_parameter("stroke_color", $datum, @param_path ) ),
				 );

		printsvg($svg);

		my $thickness = seek_parameter( "stroke_thickness", $datum, @param_path );
		my $stroke_color = seek_parameter( "stroke_color", $datum, @param_path );
		my $color_obj;
		if($thickness == 1 && rgb_color_opacity($stroke_color) == 1) {
		  # this is a 1-px thick line and the color has no transparency - 
		  # go ahead and antialias this line
		  $IM->setAntiAliased($COLORS->{$stroke_color});
		  $color_obj = gdAntiAliased;
		} else {
		  $IM->setThickness($thickness) if $thickness > 1;
		  $color_obj = $COLORS->{$stroke_color};
		}
		$IM->polygon( $poly, $color_obj ) if $PNG_MAKE;
	      }
	    }
	  }
	} elsif ( $plot_type eq "line" || $plot_type eq "histogram" ) {
	  my $url = seek_parameter("url",$data_point,$datum,@param_path);
	  $url = format_url(url=>$url,param_path=>[$data_point,$datum,@param_path]);
	  #
	  # check whether adjacent points on the same ideogram are
	  # within the max_gap distance,
	  #
	  my $gap_pass = 1;
	  if (   $data_point_prev
		 && $data_point_prev->{ideogram_idx} ==
		 $data_point->{ideogram_idx}
	     ) {
	    my ( $xp, $yp ) =
	      getxypos( @{$data_point_prev}{qw(angle radius)} );
	    my ( $x, $y ) =
	      getxypos( @{$data_point}{qw(angle radius)} );

	    if ( seek_parameter( "max_gap", @param_path ) ) {
	      my $max_gap =
		seek_parameter( "max_gap", @param_path );

	      unit_validate( $max_gap, "plots/plot/max_gap",
			     qw(u n p b) );

	      my ( $max_gap_value, $max_gap_unit ) =
		unit_split( $max_gap, "plots/plot/max_gap" );

	      if ( $max_gap_unit =~ /[bun]/ ) {
		$max_gap_value = unit_convert(
					      from => $max_gap,
					      to   => "b",
					      factors =>
					      {
					       ub => $CONF{chromosomes_units} }
					     ) if $max_gap_unit eq "u";

		my $d = abs(
			    (
			     $data_point_prev->{start} +
			     $data_point_prev->{end}
			    ) / 2 - (
				     $data_point->{start} +
				     $data_point->{end}
				    ) / 2
			   );

		$gap_pass = $d <= $max_gap_value;
	      } else {
		my $d =
		  sqrt( ( $xp - $x )**2 + ( $yp - $y )**2 );
		$gap_pass = $d <= $max_gap_value;
	      }
	    }

	    if ( !$gap_pass ) {
	      goto SKIPDATUM
		if !$gap_pass && $plot_type eq "line";
	    }
	  } else {
	    $data_point_prev = undef;
	  }

	  my $thickness = seek_parameter( "thickness", $datum, @param_path );
	  my ( $line_brush, $line_colors ) = fetch_brush(
							 seek_parameter( "thickness", $datum, @param_path ),
							 seek_parameter( "thickness", $datum, @param_path )
							);

	  my $color1 = seek_parameter( "color", $datum_prev || $datum,
				       @param_path );

	  my $color2 = seek_parameter( "color", $datum, @param_path );

	  if ( $plot_type eq "line" ) {
	    goto SKIPDATUM unless $data_point_prev;
	    goto SKIPDATUM
	      if $data_point->{ideogram_idx} !=
		$data_point_next->{ideogram_idx};
	    goto SKIPDATUM
	      if $data_point->{ideogram_idx} !=
		$data_point_prev->{ideogram_idx};
	    my ( $xp, $yp ) =
	      getxypos( @{$data_point_prev}{qw(angle radius)} );
	    my ( $x, $y ) =
	      getxypos( @{$data_point}{qw(angle radius)} );

	    if ( $color1 ne $color2 ) {
	      draw_line(
			[
			 $xp, $yp,
			 ( $x + $xp ) / 2,
			 ( $y + $yp ) / 2
			],
			$thickness,
			$color1
		       );
	      draw_line(
			[
			 ( $x + $xp ) / 2,
			 ( $y + $yp ) / 2,
			 $x, $y
			],
			$thickness,
			$color2
		       );

	    } else {
	      draw_line(
			[
			 $xp, $yp, $x, $y
			],
			$thickness,
			$color1
		       );
	    }
	  } elsif ( $plot_type eq "histogram" ) {

	    my $first_on_ideogram;
	    my $last_on_ideogram;

	    if (  !$data_point_prev
		  || $data_point_prev->{ideogram_idx} !=
		  $data_point->{ideogram_idx} ) {
	      $first_on_ideogram = 1;
	    }

	    if ( !defined $data_point_next
		 || $data_point->{ideogram_idx} !=
		 $data_point_next->{ideogram_idx} ) {
	      $last_on_ideogram = 1;
	    }

	    my $join_bins;

	    # 
	    # present bin will be joined to previous one if
	    # - previous bin exists, and
	    # - bin extension has not been explicitly defined 
	    #   to "no", or
	    # - previous bin end is within 1bp of the current 
	    #   bin start
	    # 
	    if (
		$data_point_prev
		&& $gap_pass
		&& $data_point_prev->{ideogram_idx} ==
		$data_point->{ideogram_idx}
		&& (
		    !defined seek_parameter( "extend_bin", $datum,
					     @param_path )
		    || seek_parameter( "extend_bin", $datum,
				       @param_path )
		    || abs(
			   $data_point->{start} -
			   $data_point_prev->{end}
			  ) <= 1
		   )
	       ) {
	      $join_bins = 1;
	    }

	    my $color1 =
	      seek_parameter( "color", $datum_prev || $datum,
			      @param_path );

	    my $color2 =
	      seek_parameter( "color", $datum, @param_path );

	    if ( !$join_bins ) {
	      # bins are not joined
	      if (seek_parameter("fill_under", $datum, @param_path)) {
		# floor of bin is 0 level
		slice(
		      image       => $IM,
		      start       => $data_point->{start},
		      end         => $data_point->{end},
		      chr         => $data_point->{chr},
		      radius_from => $radius0
		      ,		#$orientation eq "in" ? $r1 : $r0,
		      radius_to => $data_point->{radius},
		      fillcolor => seek_parameter(
						  "fill_color", $datum, @param_path
						 ),
		      edgecolor  => $color2,
		      edgestroke => 0,
		      mapoptions => {url=>$url},
		     );
	      }
	      # draw drop end of previous bin
	      slice(
		    image       => $IM,
		    start       => $data_point_prev->{end},
		    end         => $data_point_prev->{end},
		    chr         => $data_point_prev->{chr},
		    radius_from => $data_point_prev->{radius},
		    radius_to =>
		    $radius0,   #$orientation eq "in" ? $r1 : $r0,
		    edgecolor  => $color1,
		    edgestroke => seek_parameter(
						 "thickness", $datum, @param_path
						)
		   ) if $data_point_prev && !$first_on_ideogram;
	      # draw drop start of current bin
	      slice(
		    image       => $IM,
		    start       => $data_point->{start},
		    end         => $data_point->{start},
		    chr         => $data_point->{chr},
		    radius_from => $data_point->{radius},
		    radius_to =>
		    $radius0,   #$orientation eq "in" ? $r1 : $r0,
		    edgecolor  => $color2,
		    edgestroke => seek_parameter(
						 "thickness", $datum, @param_path
						)
		   );
	      # draw roof of current bin
	      slice(
		    image       => $IM,
		    start       => $data_point->{start},
		    end         => $data_point->{end},
		    chr         => $data_point->{chr},
		    radius_from => $data_point->{radius},
		    radius_to   => $data_point->{radius},
		    edgecolor   => $color2,
		    edgestroke  => seek_parameter(
						  "thickness", $datum, @param_path
						 )
		   );
	    } else {
	      # bins are joined
	      my ( $pos_prev_end, $pos_start, $pos_end );
	      $pos_prev_end = $data_point_prev->{end};
	      $pos_start =
		( $data_point_prev->{end} + $data_point->{start} )
		  / 2;
	      $pos_end = $data_point->{end};

	      # bins are joined
	      if (seek_parameter("fill_under", $datum, @param_path)) {
		slice(
		      image       => $IM,
		      start       => $pos_prev_end,
		      end         => $pos_start,
		      chr         => $data_point_prev->{chr},
		      radius_from => $radius0
		      ,		#$orientation eq "in" ? $r1 : $r0,
		      radius_to => $data_point_prev->{radius},
		      fillcolor => seek_parameter(
						  "fill_color", $datum_prev,
						  @param_path
						 ),
		      edgecolor  => $color1,
		      edgestroke => 0,
		      mapoptions => {url=>$url},
		     );
		slice(
		      image       => $IM,
		      start       => $pos_start,
		      end         => $pos_end,
		      chr         => $data_point->{chr},
		      radius_from => $radius0
		      ,		#$orientation eq "in" ? $r1 : $r0,
		      radius_to => $data_point->{radius},
		      fillcolor => seek_parameter(
						  "fill_color", $datum, @param_path
						 ),
		      edgecolor  => $color2,
		      edgestroke => 0,
		      mapoptions => {url=>$url},
		     ) if seek_parameter( "fill_under", $datum,@param_path );
	      }
	      slice(
		    image       => $IM,
		    start       => $pos_prev_end,
		    end         => $pos_start,
		    chr         => $data_point_prev->{chr},
		    radius_from => $data_point_prev->{radius},
		    radius_to   => $data_point_prev->{radius},
		    edgecolor   => $color1,
		    edgestroke  => seek_parameter("thickness", $datum, @param_path)
		   );

	      if ( $color1 ne $color2 ) {
		my ( $r_min, $r_max, $join_color ) =
		  abs( $data_point_prev->{radius} - $radius0 ) <
		    abs( $data_point->{radius} - $radius0 )
		      ? (
			 $data_point_prev->{radius},
			 $data_point->{radius}, $color2
			)
			: (
			   $data_point->{radius},
			   $data_point_prev->{radius}, $color1
			  );

		if ( ( $r_min < $radius0 && $r_max > $radius0 )
		     || ( $r_max < $radius0
			  && 
			  $r_min > $radius0 )
		   ) {
		  slice(
			image => $IM,
			start => $pos_start,
			end   => $pos_start,
			chr   => $data_point_prev->{chr},
			radius_from =>
			$data_point_prev->{radius},
			radius_to  => $radius0,
			edgecolor  => $color1,
			edgestroke => seek_parameter("thickness", $datum, @param_path)
		       );

		  slice(
			image => $IM,
			start => $pos_start,
			end   => $pos_start,
			chr   => $data_point_prev->{chr},
			radius_from => $radius0,
			radius_to   => $data_point->{radius},
			edgecolor   => $color2,
			edgestroke  => seek_parameter("thickness", $datum, @param_path)
		       );
		} else {
		  slice(
			image       => $IM,
			start       => $pos_start,
			end         => $pos_start,
			chr         => $data_point_prev->{chr},
			radius_from => $r_min,
			radius_to   => $r_max,
			edgecolor  => $join_color,
			edgestroke => seek_parameter("thickness", $datum, @param_path)
		       );
		}
	      } else {
		slice(
		      image       => $IM,
		      start       => $pos_start,
		      end         => $pos_start,
		      chr         => $data_point_prev->{chr},
		      radius_from => $data_point_prev->{radius},
		      radius_to   => $data_point->{radius},
		      edgecolor   => seek_parameter("color", $datum, @param_path),
		      edgestroke => seek_parameter("thickness", $datum, @param_path)
		     );
	      }
	      slice(
		    image       => $IM,
		    start       => $pos_start,
		    end         => $pos_end,
		    chr         => $data_point_prev->{chr},
		    radius_from => $data_point->{radius},
		    radius_to   => $data_point->{radius},
		    edgecolor   => $color2,
		    edgestroke  => seek_parameter("thickness", $datum, @param_path)
		   );
	    }

	    # 
	    # for bins that are first/last on this ideogram, make
	    # sure that the drop line from the start/end of the bin
	    # is drawn
	    # 
	    if ($first_on_ideogram) {
	      slice(
		    image       => $IM,
		    start       => $data_point->{start},
		    end         => $data_point->{start},
		    chr         => $data_point->{chr},
		    radius_from => $data_point->{radius},
		    radius_to   => $radius0,   
		    edgecolor   => $color2,
		    edgestroke  => seek_parameter("thickness", $datum, @param_path)
		   );
	    }

	    if ($last_on_ideogram) {
	      slice(
		    image       => $IM,
		    start       => $data_point->{end},
		    end         => $data_point->{end},
		    chr         => $data_point->{chr},
		    radius_from => $data_point->{radius},
		    radius_to   => $radius0,   
		    #$orientation eq "in" ? $r1 : $r0,
		    edgecolor  => $color2,
		    edgestroke => seek_parameter("thickness", $datum, @param_path)
		   );
	    }
	  }
	} elsif ( $plot_type eq "tile" ) {
	  my $set;
	  eval {
	    $set = Set::IntSpan->new(
				     sprintf( "%d-%d",
					      $data_point->{start}, $data_point->{end} )
				    );
	  };

	  if ($@) {
	    printinfo( "error - badtileset", $datum->{pos} );
	    next;
	  }

	  my $padded_set = Set::IntSpan->new(
					     sprintf( "%d-%d",
						      $set->min - $margin,
						      $set->max + $margin )
					    );

	  my ($freelayer) =
	    grep( !$_->{set}->intersect($padded_set)->cardinality,
		  @{ $tilelayers[$ideogram_idx] } );

	  my $color = seek_parameter( "color", $datum->{data}[0],
				      $datum, @param_path );

	  my $markup =
	    seek_parameter( "layers_overflow_color", @param_path );

	  if ( !$freelayer ) {
	    my $overflow =
	      seek_parameter( "layers_overflow", @param_path );

	    if ( $overflow eq "hide" ) {

	      # not plotting this data point
	      goto SKIPDATUM;
	    } elsif ( $overflow eq "collapse" ) {
	      $freelayer = $tilelayers[$ideogram_idx][0];
	    } else {
	      push @{ $tilelayers[$ideogram_idx] },
		{
		 set => Set::IntSpan->new(),
		 idx => int( @{ $tilelayers[$ideogram_idx] } )
		};
	      $freelayer = $tilelayers[$ideogram_idx][-1];
	    }

	    $color =
	      seek_parameter( "layers_overflow_color",
			      $datum->{data}[0],
			      $datum, @param_path )
		if $markup;
	  }

	  if ( 
	      $freelayer->{idx} >=
	      seek_parameter( "layers", @param_path ) 
	      && $markup 
	     ) {
	    $color =
	      seek_parameter( "layers_overflow_color",
			      $datum->{data}[0],
			      $datum, @param_path ),
				;
	  }

	  $freelayer->{set} = $freelayer->{set}->union($padded_set);
	  my $radius;
	  my $t = seek_parameter( "thickness", $datum->{data}[0],
				  $datum, @param_path );
	  my $p = seek_parameter( "padding", $datum->{data}[0],
				  $datum, @param_path );

	  if ( $orientation eq "out" ) {
	    $radius = $r0 + $freelayer->{idx} * ( $t + $p );
	  } elsif ( $orientation eq "in" ) {
	    $radius = $r1 - $freelayer->{idx} * ( $t + $p );
	  } else {
	    my $nlayers = seek_parameter( "layers", @param_path );
	    my $midradius = ( $r1 + $r0 ) / 2;

	    #  orientation direction
	    #      in         -1
	    #      out         1cu
	    #      center      1
	    if ( not $nlayers % 2 ) {
	      # even number of layers
	      if ( !$freelayer->{idx} ) {

                                # first layer lies below mid-point
		$radius = $midradius - $p / 2 - $t;
	      } elsif ( $freelayer->{idx} % 2 ) {

                                # 1,3,5,... layer - above mid-point
		my $m = int( $freelayer->{idx} / 2 );
		$radius =
		  $midradius + $p / 2 + $m * ( $t + $p );
	      } else {

                                # 2,4,6,... layer - below mid-point
		my $m = int( $freelayer->{idx} / 2 );
		$radius =
		  $midradius - $p / 2 - $m * ( $t + $p ) - $t;
	      }
	    } else {
	      # odd number of layers
	      if ( !$freelayer->{idx} ) {
		$radius = $midradius - $t / 2;
	      } elsif ( $freelayer->{idx} % 2 ) {

                                # 1,3,5,... layer - above mid-point
		my $m = int( $freelayer->{idx} / 2 );
		$radius =
		  $midradius + $t / 2 + $m * ( $p + $t ) + $p;
	      } else {

                                # 2,4,6,... layer - below mid-point
		my $m = int( $freelayer->{idx} / 2 );
		$radius =
		  $midradius - $t / 2 - $m * ( $p + $t );
	      }
	    }
	  }
	  my $url = seek_parameter("url",$data_point,$datum,@param_path);
	  $url = format_url(url=>$url,param_path=>[$data_point,$datum,@param_path]);
	  #printinfo($url);
	  slice(
		image       => $IM,
		start       => $set->min,
		end         => $set->max,
		chr         => $data_point->{chr},
		radius_from => $radius,
		radius_to   => $radius +
		$orientation_direction * seek_parameter(
							"thickness", $datum->{data}[0],
							$datum,      @param_path
						       ),
		edgecolor => seek_parameter(
					    "stroke_color", $datum->{data}[0],
					    $datum,         @param_path
					   ),
		edgestroke => seek_parameter(
					     "stroke_thickness", $datum->{data}[0],
					     $datum,             @param_path
					    ),
		mapoptions => { url=>$url },
		fillcolor => $color,
	       );
	} elsif ( $plot_type eq "histogram" ) {
	  my ( $line_brush, $line_colors ) = fetch_brush(
							 seek_parameter(
									"stroke_thickness", $datum, @param_path
								       ),
							 seek_parameter(
									"stroke_thickness", $datum, @param_path
								       ),
							 seek_parameter( "stroke_color", $datum, @param_path )
							);

	  if ( $prevpoint && $prevpoint->{chr} eq $datum->{chr} ) {
	    if (
		!defined seek_parameter( "break_line_distance",
					 $datum, $dataset, $plot )
		|| abs( $prevpoint->{start} - $datum->{start} ) <=
		seek_parameter(
			       "break_line_distance",
			       $datum, $dataset, $plot
			      )
	       ) {
	      my $midpos =
		( $prevpoint->{start} + $datum->{start} ) / 2;
	      my $midangle =
		getanglepos( $midpos, $datum->{chr} );
	      if (seek_parameter("fill_under", $datum, $dataset, $plot)) {
		slice(
		      image       => $IM,
		      start       => $prevpoint->{start},
		      end         => $midpos,
		      chr         => $datum->{chr},
		      radius_from => $r0,
		      radius_to   => $prevpoint->{radius},
		      edgecolor   => seek_parameter(
						    "color", $datum, $dataset, $plot
						   ),
		      edgestroke => 0,
		      fillcolor  => seek_parameter(
						   "color", $datum, $dataset, $plot
						  )
		     );

		slice(
		      image       => $IM,
		      start       => $midpos,
		      end         => $datum->{start},
		      chr         => $datum->{chr},
		      radius_from => $r0,
		      radius_to   => $radius,
		      edgecolor   => seek_parameter(
						    "color", $datum, $dataset, $plot
						   ),
		      edgestroke => 0,
		      fillcolor  => seek_parameter(
						   "color", $datum, $dataset, $plot
						  )
		     );
	      }

	      slice(
		    image       => $IM,
		    start       => $prevpoint->{start},
		    end         => $midpos,
		    chr         => $datum->{chr},
		    radius_from => $prevpoint->{radius},
		    radius_to   => $prevpoint->{radius},
		    edgestroke  => seek_parameter(
						  "stroke_thickness",
						  $datum, $dataset, $plot
						 ),
		    edgecolor => seek_parameter(
						"stroke_color", $datum, $dataset, $plot
					       )
		   );

	      slice(
		    image       => $IM,
		    start       => $midpos,
		    end         => $datum->{start},
		    chr         => $datum->{chr},
		    radius_from => $radius,
		    radius_to   => $radius,
		    edgestroke  => seek_parameter(
						  "stroke_thickness",
						  $datum, $dataset, $plot
						 ),
		    edgecolor => seek_parameter(
						"stroke_color", $datum, $dataset, $plot
					       )
		   );

	      draw_line(
			[
			 getxypos( $midangle, $prevpoint->{radius} ),
			 getxypos( $midangle, $radius ),
			 ],
			seek_parameter( "stroke_thickness", $datum, @param_path ),
			seek_parameter( "stroke_color", $datum, @param_path )
		       );
	    }
	  }
	} elsif ( $plot_type eq "heatmap" ) {
	  my @colors = split(
			     /[\s+,]+/,
			     seek_parameter(
					    "color", $datum->{data}[0],
					    $datum, @param_path
					   )
			    );

	  my $value = $data_point->{value};
	  my $color_index;
	  if ( $value > $plot_max ) {
	    $color_index = @colors - 1;
	  } elsif ( $value < $plot_min ) {
	    $color_index = 0;
	  } elsif ( seek_parameter( "scale_log_base", @param_path ) ) {
	    my $base = seek_parameter( "scale_log_base", @param_path );
	    die "The scale_log_base parameter for a heat map cannot be zero or negative. Please change it to a non-zero positive value or remove it." unless $base>0;
	    my $f = ( $value - $plot_min ) / ( $plot_max - $plot_min );
	    my $flog = $f**( 1 / $base );
	    $color_index = ( @colors - 1 ) * $flog;
	  } else {
	    my $d = $plot_max - $plot_min;
	    $color_index = $d ? (@colors-1)*($value-$plot_min)/$d : 0;
	  }

	  my $color = $colors[$color_index];
	  my $url = seek_parameter("url",$data_point,$datum,@param_path);
	  $url = format_url(url=>$url,param_path=>[{color=>$color},
						   $data_point,$datum,@param_path]);
	  slice(
		image       => $IM,
		start       => $data_point->{start},
		end         => $data_point->{end},
		chr         => $data_point->{chr},
		radius_from => $r0,
		radius_to   => $r1,
		edgecolor   => seek_parameter(
					      "stroke_color", $datum->{data}[0],
					      $datum,         @param_path
					     ),
		edgestroke => seek_parameter(
					     "stroke_thickness", $datum->{data}[0],
					     $datum,             @param_path
					    ),
		mapoptions => {url=>$url},
		fillcolor => $color,
	       );
	}

      SKIPDATUM:
	$datum_prev      = $datum;
	$data_point_prev = $data_point;
      }

      printsvg(qq{</g>}) if $SVG_MAKE;
      $plotid++;
    }
  }

 OUT:

  if ($MAP_MAKE) {
    for my $map_element (reverse @MAP_ELEMENTS) {
      printf MAP $map_element->{string},"\n";
      if($CONF{image}{image_map_overlay}) {
	# create an overlay of the image map elements
	my $poly = GD::Polygon->new();
	my @coords = map {round($_)} @{$map_element->{coords}};
	if(@coords == 3) {
	  if($CONF{image}{image_map_overlay_fill_color}) {
	    $IM->filledArc(
		     @coords,
		     $coords[2],
		     0, 360,
		     aa_color($CONF{image}{image_map_overlay_fill_color},$IM,$COLORS)
		    );
	  }
	  my $color_obj;
	  if($CONF{image}{image_map_overlay_stroke_thickness}) {
	    $IM->setThickness($CONF{image}{image_map_overlay_stroke_thickness});
	    $color_obj = $COLORS->{$CONF{image}{image_map_overlay_stroke_color}};
	  } else {
	    $color_obj = aa_color($CONF{image}{image_map_overlay_stroke_color},$IM,$COLORS);
	  }
	  if($CONF{image}{image_map_overlay_stroke_color}) {
	    $IM->arc(
		     @coords,
		     $coords[2],
		     0, 360,
		     $color_obj,
		    );
	  }
	  if($CONF{image}{image_map_overlay_stroke_thickness}) {
	    $IM->setThickness(1);
	  }
	} else {
	  while(my ($x,$y) = splice(@coords,0,2)) {
	    $poly->addPt($x,$y);
	  }
	  if($CONF{image}{image_map_overlay_fill_color}) {
	    $IM->filledPolygon($poly,
			       aa_color($CONF{image}{image_map_overlay_fill_color},$IM,$COLORS));
	  }
	  my $color_obj;
	  if($CONF{image}{image_map_overlay_stroke_thickness}) {
	    $IM->setThickness($CONF{image}{image_map_overlay_stroke_thickness});
	    $color_obj = $COLORS->{$CONF{image}{image_map_overlay_stroke_color}};
	  } else {
	    $color_obj = aa_color($CONF{image}{image_map_overlay_stroke_color},$IM,$COLORS);
	  }
	  if($CONF{image}{image_map_overlay_stroke_color}) {
	    print $IM->polygon($poly,$color_obj);
	  }
	  if($CONF{image}{image_map_overlay_stroke_thickness}) {
	    $IM->setThickness(1);
	  }
	}
      }
    }
    printf MAP "</map>\n";
    close(MAP);
    printinfo("created image map at $outputfile_map");
  }

  if ($PNG_MAKE) {
    if ( $CONF{tagname} ) {
      printinfo("tagging with $outputfile");
      $IM->stringFT(
		    $COLORS->{black},
		    locate_file(
				file =>
				$CONF{fonts}{ $CONF{ideogram}{label_font} || "default" }
			       ),
		    unit_strip( $CONF{ideogram}{label_size}, "p" ),
		    0,
		    unit_strip( $CONF{ideogram}{label_size}, "p" ),
		    1.5 * unit_strip( $CONF{ideogram}{label_size}, "p" ),
		    $outputfile
		   );
    }

    open PNG, '>', $outputfile_png 
      || confess "Cannot open output file $outputfile_png: $!\n";
    binmode PNG;
    print PNG $IM->png;
    close(PNG);
    printinfo("created image at $outputfile_png");
  }

  if ($SVG_MAKE) {
    printsvg(q{</svg>});
    close(SVG);
    printinfo("created image at $outputfile_svg");
  }

  return 1;
}

sub round_up {
  my $value = shift;
  if($value - int($value) > 0.5) {
    return round($value);
  } else {
    return 1 + int($value);
  }
}
# -------------------------------------------------------------------
sub fetch_brush {
  # given a brush size, try to fetch it from the brush
  # hash, otherwise create and store the brush.
  my ( $w, $h, $color ) = @_;
  my $brush;
  my $brush_colors;
  $w ||= 0;
  $h ||= 0;

  if ( exists $IM_BRUSHES->{size}{$w}{$h}{brush} ) {
    ( $brush, $brush_colors ) =
      @{ $IM_BRUSHES->{size}{$w}{$h} }{qw(brush colors)};
  } else {
    eval {
      if ( $w && $h ) {

	#printinfo("creating full brush",$w,$h);
	$brush = GD::Image->new( $w, $h, $CONF{image}{"24bit"} );
      } else {

	#printinfo("creating empty brush",$w,$h);
	if ( $CONF{image}{"24bit"} ) {
	  $brush = GD::Image->newTrueColor();
	} else {
	  $brush = GD::Image->new();
	}
      }
    };

    if ($@) {
      croak "error - could not create 24-bit brush in fetch_brush"
	if $CONF{image}{"24bit"};
      if ( $w && $h ) {
	$brush = GD::Image->new( $w, $h );
      } else {
	$brush = GD::Image->new();
      }
    }

    if ( !$brush ) {
      croak "error - could not create brush of size ($w) x ($h)";
    }

    $brush_colors = allocate_colors($brush);

    @{ $IM_BRUSHES->{size}{$w}{$h} }{qw(brush colors)} =
      ( $brush, $brush_colors );
  }

  if ( defined $color && $w && $h ) {
    $brush->fill( 0, 0, $brush_colors->{$color} );
  }

  return ( $brush, $brush_colors );
}

# -------------------------------------------------------------------
sub span_from_pair {
  return Set::IntSpan->new( sprintf( "%d-%d", @_ ) );
}

# -------------------------------------------------------------------
sub angle_to_span {
  my $angle      = shift;
  my $resolution = shift;
  my $shift      = shift;
  return ( $angle + $shift - $CONF{image}{angle_offset} ) * $resolution;
}

# -------------------------------------------------------------------
sub rotate_xy {
  #
  # Using a link, or any other data, apply a conditional formatting
  # rule. Any strings of the format _VARIABLE{NUM}_ in the
  # rule string is parsed and replaced by the value of point NUM's
  # VARIABLE
  #
  my ( $x, $y, $x0, $y0, $angle ) = @_;
  $angle = ( $angle - $CONF{image}{angle_offset} ) * $PI / 180;
  my $xr = ( $x - $x0 ) * cos($angle) - ( $y - $y0 ) * sin($angle);
  my $yr = ( $x - $x0 ) * sin($angle) + ( $y - $y0 ) * cos($angle);
  return ( round( $xr + $x0 ), round( $yr + $y0 ) );
}

# -------------------------------------------------------------------
sub format_condition {
  #
  # apply suffixes kb, Mb, Gb (case-insensitive) trailing any numbers
  # and apply appropriate multiplier to the number
  #
  my $condition = shift;
  $condition =~ s/([\d\.]+)kb/sprintf("%d",$1*1e3)/eig;
  $condition =~ s/([\d\.]+)Mb/sprintf("%d",$1*1e6)/eig;
  $condition =~ s/([\d\.]+)Gb/sprintf("%d",$1*1e9)/eig;
  $condition =~ s/(\d+)bp/$1/ig;
  return $condition;
}

# -------------------------------------------------------------------
sub eval_expression {
  #
  # supported fields
  #
  # _{DATA}_ where DATA is an element in the coordinate's hash
  #   e.g. _CHR_ _START_ _END_ _VALUE_
  # or in the data's parameter list
  #   e.g. _COLOR_ _THICKNESS_
  #
  # _{DATA}{N}_ where N is the index (1-indexed) of the data point
  #
  # _INTERCHR_ - returns 1 if not all chromosomes are same
  # _INTRACHR_ - returns 1 if all chromosomes are the same
  #

  my ( $datum, $condition, $param_path ) = @_;

  # (.+?) replaced by (\w+)
  while ( $condition =~ /(_(\w+)_)/ ) {
    my ( $string, $var ) = ( $1, lc $2 );
    my ( $varroot, $varnum );
    if ( $var =~ /^(.+?)(\d+)$/ ) {
      ( $varroot, $varnum ) = ( lc $1, $2 );
    } else {
      $varroot = $var;
    }

    # if this data collection has only one data value (e.g. scatter plot)
    # then assume that any expression without an explicit number is refering
    # to the data point (e.g. _SIZE_ acts like _SIZE1_)
    $varnum = 1 if @{ $datum->{data} } == 1 && !$varnum;

    # number in espression is 1-indexed but refers to 0-indexed data
    # e.g. _CHR1_ refers to {data}[0]{chr}
    $varnum-- if defined $varnum;
    debug_or_group("rule")
      && printdebug( "condition", $condition, "var", $var, "varroot",
		     $varroot );

    if ( defined $varnum ) {
      if ( $datum->{data}[$varnum] ) {
	if ( exists( $datum->{data}[$varnum]{data}{$varroot} ) ) {
	  my $value = $datum->{data}[$varnum]{data}{$varroot};
	  debug_or_group("rule")
	    && printdebug( "var", $var, "varroot", $varroot, "varnum",
			   $varnum, "value", $value );
	  replace_string( \$condition, $string, $value );
	} elsif ( exists( $datum->{data}[$varnum]{param}{$varroot} ) ) {
	  my $value = $datum->{data}[$varnum]{param}{$varroot};
	  debug_or_group("rule")
	    && printdebug( "var", $var, "varroot", $varroot, "varnum",
			   $varnum, "value", $value );
	  replace_string( \$condition, $string, $value );
	} elsif ( seek_parameter( $varroot, @$param_path ) ) {
	  my $value = seek_parameter( $varroot, @$param_path );
	  debug_or_group("rule") && printdebug(
					       "var",    $var,    "varroot", $varroot,
					       "varnum", $varnum, "value",   $value,
					       "string", $string
					      );
	  replace_string( \$condition, $string, $value );
	} elsif ( $varroot eq "size" ) {
	  my $value =
	    $datum->{data}[$varnum]{data}{end} -
	      $datum->{data}[$varnum]{data}{start} + 1;
	  replace_string( \$condition, $string, $value );
	} elsif ( $varroot eq "position" ) {
	  my $value =
	    ( $datum->{data}[$varnum]{data}{end} +
	      $datum->{data}[$varnum]{data}{start} ) / 2;
	  replace_string( \$condition, $string, $value );
	} else {
	  confess "You set up a rule [$condition] that uses ",
	    "parsable field [$string] but the data you are testing ",
	      "does not have the field [$varroot].";
	}
      } else {
	confess "You set up a rule [$condition] that uses parsable ",
	  "field [$string] but the data you are testing does not have ",
	    "[$varnum] elements.";
      }
    } else {
      if ( $varroot eq "intrachr" ) {
	my %chrs;
	for my $point ( @{ $datum->{data} } ) {
	  $chrs{ $point->{data}{chr} }++;
	}
	my $value = ( keys %chrs == 1 ) ? 1 : 0;
	replace_string( \$condition, $string, $value );
      } elsif ( $varroot eq "interchr" ) {
	my %chrs;
	for my $point ( @{ $datum->{data} } ) {
	  $chrs{ $point->{data}{chr} }++;
	}
	my $value = ( keys %chrs > 1 ) ? 1 : 0;
	replace_string( \$condition, $string, $value );
      } elsif (
	       seek_parameter(
			      $varroot, $datum, $datum->{data}, @$param_path
			     )
	      ) {
	my $value =
	  seek_parameter( $varroot, $datum, $datum->{data},
			  @$param_path );
	debug_or_group("rule") && printdebug(
					     "var",    $var,    "varroot", $varroot,
					     "varnum", $varnum, "value",   $value,
					     "string", $string
					    );
	replace_string( \$condition, $string, $value );
      } else {
	#replace_string(\$condition,$string,"undef");
	confess "You set up a rule [$condition] that uses parsable ",
	  "field [$string], but this string has no associated value.";
      }
    }
  }

  debug_or_group("rule") && printdebug( "condition", $condition );

  my $pass = eval format_condition($condition);

  confess "There was a problem parsing the condition [$condition]" if $@;

  debug_or_group("rule") && printdebug( $condition, "pass?", $pass || 0, $@ );

  return $pass;
}

# -------------------------------------------------------------------
sub replace_string {
  my ( $target, $source, $value ) = @_;
  if ( $value =~ /[^0-9-.]/ && $value ne "undef" ) {
    $$target =~ s/$source/'$value'/g;
  } else {
    $$target =~ s/$source/$value/g;
  }
}

# -------------------------------------------------------------------
sub test_rule {
  my ( $datum, $condition, $param_path ) = @_;
  $condition = format_condition($condition);
  my $pass = eval_expression( $datum, $condition, $param_path );
  return $pass;
}

# -------------------------------------------------------------------
sub perturb_value {
  #
  # Given a value and string "pmin,pmax", perturb the value
  # within the range value*pmin ... value*pmax, sampling
  # from the range uniformly
  #
  my ( $value, $perturb_parameters ) = @_;

  return $value if !$perturb_parameters || !$value;

  my ( $pmin, $pmax ) = split( /[\s,]+/, $perturb_parameters );
  my $prange          = $pmax - $pmin;
  my $urd             = $pmin + $prange * rand();
  my $new_value       = $value * $urd;

  return $new_value;
}

# -------------------------------------------------------------------
sub draw_bezier {
  # draw the bezier curve on a bitmap image
  # We are not using a brush anymore to draw thick lines, but rather setThickness($thickness).
  my ( $points, $thickness, $color ) = @_;

  # if we're not making a bitmap, this function is not used
  return if !$PNG_MAKE;
  if ( $thickness > 100 ) {
    confess "error - you are attempting to draw a bezier curve of ",
      "thickness greater than 100 [$thickness]. This would take a ",
        "very long time and you don't want to do this.";
  } elsif ( $thickness < 1 ) {
    confess "error - you are attempting to draw a bezier curve of ",
      "thickness less than 1 [$thickness]. This would produce nothing. ",
        "Is this what you want?";
  }

  # In the current implementation of gd (2.0.35) antialiasing is
  # incompatible with thick lines and transparency. Thus, antialiased lines
  # are available only when thickness=1 and the color has no alpha channel.

  my $line_color_obj;
  if($thickness == 1 && rgb_color_opacity($color) == 1) {
    # this is a 1-px thick line and the color has no transparency - 
    # go ahead and antialias this line
    $IM->setAntiAliased($COLORS->{$color});
    $line_color_obj = gdAntiAliased;
  } else {
    $IM->setThickness($thickness) if $thickness > 1;
    $line_color_obj = $COLORS->{$color};
  }

  # todo - when a polyline is drawn, adjacent line
  # segments overlap by 1px. When transparency is used, this
  # creates a darker spot along the line, at beziersamples positions.
  # fix this by drawing the line segments independently, and adjusting
  # the end position of each segment

  my $bezier_poly_line = GD::Polyline->new();
  for my $i ( 0 .. @$points - 1 ) {
    $bezier_poly_line->addPt(@{$points->[$i]});
  }
  my $spline = $bezier_poly_line->addControlPoints->toSpline;
  $IM->polydraw($bezier_poly_line,$line_color_obj);
  # return thickness to 1px
  $IM->setThickness(1) if $thickness > 1;
}

sub aa_color {
  my ($color,$im,$imcolors) = @_;
  if(rgb_color_opacity($color) == 1) {
    $im->setAntiAliased( $imcolors->{$color} );
    return gdAntiAliased;
  } else {
    $imcolors->{$color};
  }
}

# -------------------------------------------------------------------
sub draw_line {
  # draw the bezier curve
  # We are not using a brush anymore to draw thick lines, but rather setThickness($thickness).
  my ( $points, $thickness, $color ) = @_;

  if($PNG_MAKE) {
    my $line_color_obj;
    # In the current implementation of gd (2.0.35) antialiasing is
    # incompatible with thick lines and transparency. Thus, antialiased lines
    # are available only when thickness=1 and the color has no alpha channel.
    if($thickness == 1 && rgb_color_opacity($color) == 1) {
      # this is a 1-px thick line and the color has no transparency - 
      # go ahead and antialias this line
      $IM->setAntiAliased($COLORS->{$color});
      $line_color_obj = gdAntiAliased;
    } else {
      $IM->setThickness($thickness) if $thickness > 1;
      $line_color_obj = $COLORS->{$color};
    }
    $IM->line( @$points, $line_color_obj );
    $IM->setThickness(1) if $thickness > 1;
  }

  # svg line
  my $svg = sprintf(
		    '<line x1="%.1f" y1="%.1f" x2="%.1f" y2="%.1f" style="stroke-width: %.1f; stroke: rgb(%d,%d,%d); stroke-linecap: round;" />',
		    @$points, 
		    $thickness, 
		    rgb_color($color), 
		   );

  printsvg($svg);
}

# -------------------------------------------------------------------
sub seek_parameter {
  # Given a parameter name and a list of hash references (or list
  # references to hashes), looks for the parameter and returns the
  # associated value. The parameter will also be extracted from any
  # hash pointed to by the "param" key in the data structure.
  #
  # If the parameter name contains "|" then this is used as a
  # delimiter to define synonyms of the parameter. This is helpful
  # when parameters have changed names but you wish to maintain
  # backward compatibility.
  #
  # value of x returned from $hash
  # seek_parameter("x",$hash);
  # value of x returned from $hash, and if not found, $anotherhash is tried
  # seek_parameter("x",$hash,$anotherhash);
  # value of x or y, whichever is seen first is returned
  # seek_parameter("x|y",$hash,$anotherhash);
  my ( $param_name, @data_structs ) = @_;
  my @target_string = split( /\|/, $param_name );

  for my $str (@target_string) {
    for my $struct (@data_structs) {
      if ( ref($struct) eq "ARRAY" ) {
	for my $substruct (@$struct) {
	  return $substruct->{param}{$str}
	    if exists $substruct->{param}
	      && defined $substruct->{param}{$str};
	  return $substruct->{$str}
	    if exists $substruct->{$str}
	      && defined $substruct->{$str};
	}
      } elsif ( ref($struct) eq "HASH" ) {
	return $struct->{param}{$str}
	  if exists $struct->{param} && defined $struct->{param}{$str};
	return $struct->{$str}
	  if exists $struct->{$str} && defined $struct->{$str};
      } else {
	printdumper(\@data_structs);
	croak "cannot extract parameter from this data structure (shown above - report this please)";
      }
    }
  }
  return undef;
}

# -------------------------------------------------------------------
sub draw_highlights {
  # Draw hilight data for a given chromosome. If a test
  # is included, then only highlights whose options pass
  # the test will be drawn.
  #
  # The test is a hash of variable=>value pairs.

  my ( $datasets, $chr, $set, $ideogram, $test ) = @_;
  my $highlightid = 0;
  for my $highlight_set ( make_list( $datasets->{dataset} ) ) {
    printsvg(qq{<g id="highlight$highlightid">}) if $SVG_MAKE;
    $highlightid++;
    # create a working list of highlights at a given z-depth
    next unless ref( $highlight_set->{data} ) eq "ARRAY";
    my $working_list;
    for my $data ( map { $_->{data}[0] } @{ $highlight_set->{data} } ) {
      next unless $data->{data}{chr} eq $chr;
      my $z = seek_parameter( "z", $data, $highlight_set, $datasets ) || 0;
      push @{$working_list->{$z}}, $data;
    }
    for my $targetz ( @{ $datasets->{param}{zlist} } ) {
      #printinfo($targetz);
      #next unless ref( $highlight_set->{data} ) eq "ARRAY";
      for my $data (@{$working_list->{$targetz}}) {
	#for my $data ( map { $_->{data}[0] } @{ $highlight_set->{data} } ) {
	#next unless $data->{data}{chr} eq $chr;
	my $z = seek_parameter( "z", $data, $highlight_set, $datasets );
	#next unless defined ($z && $z == $targetz) || (! $z && ! $targetz);
	my $dataset = Set::IntSpan->new(sprintf("%d-%d", 
						$data->{data}{start}, 
						$data->{data}{end}
					       )
				       );
	next unless $set->intersect($dataset)->cardinality;
	my $set = filter_data( $dataset, $chr );
	my $r0  = seek_parameter( "r0", $data, $highlight_set, $datasets );
	my $r1  = seek_parameter( "r1", $data, $highlight_set, $datasets );
	$r0 = unit_parse( $r0, $ideogram );
	$r1 = unit_parse( $r1, $ideogram );
	my $accept = 1;

	if ($test) {
	  for my $param ( keys %$test ) {
	    my $value =
	      seek_parameter( $param, $data, $highlight_set,
			      $datasets );
	    $accept &&= $value == $test->{$param};
	    #printinfo("testing",$param,"expect",$test->{$param},"got",$value,"pass",$accept);
	  }
	}

	next unless $accept;

	my ( $radius_from, $radius_to );
	if (
	    seek_parameter( "ideogram", $data, $highlight_set, $datasets )
	    && !seek_parameter( "r0", $data, $highlight_set, $datasets )
	    && !seek_parameter( "r1", $data, $highlight_set, $datasets )
	   ) {
	  $radius_from =
	    $DIMS->{ideogram}{ $ideogram->{tag} }{radius_inner};
	  $radius_to =
	    $DIMS->{ideogram}{ $ideogram->{tag} }{radius_outer};
	} else {
	  $radius_from = $r0;
	  $radius_to   = $r1;
	  my $offset =
	    seek_parameter( "offset", $data, $highlight_set,
			    $datasets );
	  $r0 += $offset if $offset;
	  $r1 += $offset if $offset;
	}

	for my $set_piece ( $set->sets ) {
	  my ( $start_a, $end_a ) = (
				     getanglepos( $set_piece->min, $chr ),
				     getanglepos( $set_piece->max, $chr )
				    );

	  my $c = seek_parameter( "fill_color", $data, $highlight_set, $datasets);
	  my $url = seek_parameter( "url", $data, $highlight_set, $datasets);
	  $url = format_url(url=>$url,param_path=>[$data->{data}, 
						   $data, $highlight_set, $datasets]);
	  slice(
		image       => $IM,
		start       => $set_piece->min,
		end         => $set_piece->max,
		chr         => $data->{data}{chr},
		radius_from => $radius_from,
		radius_to   => $radius_to,
		edgecolor   => seek_parameter(
					      "stroke_color", $data,
					      $highlight_set, $datasets
					     ),
		edgestroke => seek_parameter(
					     "stroke_thickness", $data,
					     $highlight_set,     $datasets
					    ),
		fillcolor => seek_parameter(
					    "fill_color", $data, $highlight_set, $datasets
					   ),
		mapoptions => {
			       url => $url,
			      },
	       );
	}
      }
    }

    printsvg(qq{</g>}) if $SVG_MAKE;
  }
}

sub format_url {
  # given a url (although the function can be applied to any string)
  # replace all instances of [PARAM] with the value of the parameter
  # named PARAM extracted from the elements passed in the param_path
  #
  # e.g. format_url(url=>"www.domain.com/param=[ID]",param_path=>[$datum,$data]);
  my %args = @_;
  my $delim_left = "\Q[\E";
  my $delim_right = "\Q]\E";
  my $url = $args{url};
  while($url =~ /$delim_left([^$delim_right$delim_left]+)$delim_right/g) {
    my $param = $1;
    my $value = seek_parameter($param,@{$args{param_path}});
    printdebug("format_url",$url,$1,$value);
    if(! defined $value) {
      if ($CONF{image}{image_map_missing_parameter} eq "exit") {
	printdumper($args{param_path}[0]);
	confess "You have tried to use the URL $url for an image map, but the parameter in the url [$param] has no value defined for this data point or data set. To make this error go away, either (a) define the parameter, (b) set image_map_missing_parameter=blank to remove the undefined parameter from the image element, or (c) set image_map_missing_parameter=removeurl to remove the URL from the image element.";
      } elsif ($CONF{image}{image_map_missing_parameter} =~ /removeurl/) {
	# there is no value for this parameter, so return an empty url
	return undef;
      } elsif ($CONF{image}{image_map_missing_parameter} =~ /removeparam/) {
	carp "You have tried to use the URL $url for an image map, but the parameter in the url [$param] has no value defined for this data point or data set. This parameter is being removed from the URL of this element. Use the image_map_missing_parameter setting in the <image> block to adjust this behaviour.";
	$url =~ s/$delim_left$param$delim_right//g;
      } else {
	# not defined - removeparam by default
	carp "You have tried to use the URL $url for an image map, but the parameter in the url [$param] has no value defined for this data point or data set. This parameter is being removed from the URL of this element. Use the image_map_missing_parameter setting in the <image> block to adjust this behaviour.";
	$url =~ s/$delim_left$param$delim_right//g;
      }
    } else {
      $url =~ s/$delim_left$param$delim_right/$value/g;
    }
  }
  printdebug("format_url_done",$url);
  return $url;
}

################################################################
# First pass at creating a data structure of ideogram order
# groups. Each group is composed of the ideograms that it contains,
# their index within the group, and a few other helper structures
#
# n : number of ideograms in the group
# cumulidx : number of ideograms in all preceeding groups
# idx : group index
# tags : list of ideogram data
#        ideogram_idx - ideogram idx relative to default order
#        tag - tag of the ideogram (ID or user tag)
sub make_chrorder_groups {

  my $chrorder_groups = shift;
  my $chrorder        = shift;

  for my $tag (@$chrorder) {
    if ( $tag eq $CARAT ) {
      # this list has a start anchor
      confess "only one order group can have a start '^' anchor" if grep( $_->{start}, @$chrorder_groups );
      $chrorder_groups->[-1]{start} = 1;
    } elsif ( $tag eq q{$} ) {
      # this list has an end anchor
      confess "only one order group can have an end '$' anchor" if grep( $_->{end}, @$chrorder_groups );
      $chrorder_groups->[-1]{end} = 1;
    } elsif ( $tag eq $PIPE ) {
      # saw a break - create a new group
      push @{$chrorder_groups},
	{
	 idx      => scalar( @{$chrorder_groups} ),
	 cumulidx => $chrorder_groups->[-1]{n} + $chrorder_groups->[-1]{cumulidx}
	};
    } elsif ( $tag eq $DASH ) {
	push @{ $chrorder_groups->[-1]{tags} }, { tag => $tag };
	$chrorder_groups->[-1]{n} = int( @{ $chrorder_groups->[-1]{tags} } );
	$chrorder_groups->[-1]{tags}[-1]{group_idx} = $chrorder_groups->[-1]{n} - 1;
    } else {
      # add this tag and all ideograms that match it (v0.52) to the most recent group 
      my @tagged_ideograms = grep( ($_->{tag} !~ /__/ && $_->{tag} eq $tag) || ($_->{tag} =~ /__/ && $_->{chr} eq $tag) , @IDEOGRAMS );
      for my $tagged_ideogram (@tagged_ideograms) {
	push @{ $chrorder_groups->[-1]{tags} }, { tag => $tag, ideogram_idx => $tagged_ideogram->{idx} };
	$chrorder_groups->[-1]{n} = int( @{ $chrorder_groups->[-1]{tags} } );
	$chrorder_groups->[-1]{tags}[-1]{group_idx} = $chrorder_groups->[-1]{n} - 1;
      }
    }
  }
  #
  # to each tag with corresponding ideogram, add the ideogram_idx
  #
  # check that a group does not have the start and end anchor
  #
  for my $group (@$chrorder_groups) {
    if ( $group->{start} && $group->{end} ) {
      my @tags = map { $_->{tag} } @{ $group->{tags} };
      confess "you have a group with both start '^' and end '\$' ",
	"anchors (", join( $COMMA, @tags ),
	  ") and this is not supported - if you want to limit which ",
            "ideograms are drawn, use '-' in front of tags in the ",
	      "chromosomes field";
    }
    # This is now being done above (v0.52).
    #for my $tag_item ( @{ $group->{tags} } ) {
    #  my @tagged_ideograms = grep( ($_->{tag} !~ /__/ && $_->{tag} eq $tag_item->{tag}) || ($_->{tag} =~ /__/ && $_->{chr} eq $tag_item->{tag}) , @IDEOGRAMS );
    #  $tag_item->{ideogram_idx} = [ map {$_->{idx}} @tagged_ideograms ] if @tagged_ideograms;
    #}
  }
  return $chrorder_groups;
}

# -------------------------------------------------------------------
sub filter_data {
  my ( $set, $chr ) = @_;
  my $int = $set->intersect( 
			    $KARYOTYPE->{$chr}{chr}{display_region}{accept} 
			   );
  return $int;
}

################################################################
#
# Given the initial chromosome order groups (see make_chrorder_groups),
# set the display index of each ideogram.
#
sub set_display_index {
  my $chrorder_groups  = shift;
  my $seen_display_idx = Set::IntSpan->new();
  #
  # keep track of which display_idx values have been used
  # process groups that have start or end flags first
  #
  for my $group (sort { ( $b->{start} || $b->{end} ) <=> ( $a->{start} || $a->{end} ) } @$chrorder_groups ) {
    if ( $group->{start} ) {
      my $display_idx = 0;
      for my $tag_item ( @{ $group->{tags} } ) {
	$tag_item->{display_idx} = $display_idx;
	$seen_display_idx->insert($display_idx);
	$display_idx++;
      }
    } elsif ( $group->{end} ) {
      my $display_idx = @IDEOGRAMS - $group->{n};
      for my $tag_item ( @{ $group->{tags} } ) {
	$tag_item->{display_idx} = $display_idx;
	$seen_display_idx->insert($display_idx);
	$display_idx++;
      }
    } else {
      my $idx;
      my $minidx;

      #
      # ideogram index for first defined idoegram - this is the anchor,
      # and all other ideograms in this group have their display index
      # set relative to the anchor
      #
      my ($ideogram_anchor) = grep( defined $_->{ideogram_idx},
				    sort { $a->{group_idx} <=> $b->{group_idx} }
				    @{ $group->{tags} } );

      my $continue;
      for my $tag_item ( 
			sort { $a->{group_idx} <=> $b->{group_idx} }
			@{ $group->{tags} } 
		       ) {
	$tag_item->{display_idx} =
	  $tag_item->{group_idx} -
	    $ideogram_anchor->{group_idx} +
	      $ideogram_anchor->{ideogram_idx};
	$seen_display_idx->insert( $tag_item->{display_idx} );
      }

      #
      # find the minimum display index for this group
      #
      my $min_display_index =
	min( map { $_->{display_idx} } @{ $group->{tags} } );

      if ( $min_display_index < 0 ) {
	map { $_->{display_idx} -= $min_display_index }
	  @{ $group->{tags} };
      }
    }
  }
  return $chrorder_groups;
}

################################################################
# Create a new span object from start/end positions. 
# Positions are expected to be integers. Floats are truncated.
#
# If start>end the routine croaks.
# If start=end or end is not defined, the span is a single value.

sub newspan {
  my ($start,$end) = @_;
  if($start == $end || ! defined $end) {
    return Set::IntSpan->new(sprintf("%.0f",$start));
  } elsif ($end < $start) {
    confess "There was a problem initializing a span. Saw start>end. start=$start > end=$end";
  } else {
    return Set::IntSpan->new(sprintf("%.0f-%.0f",$start,$end));
  }
}

# -------------------------------------------------------------------
sub recompute_chrorder_groups {
  my $chrorder_groups = shift;
  my %allocated;
  my $display_idx_set = newspan(0,@IDEOGRAMS-1); #Set::IntSpan->new(sprintf( "%d-%d", 0, @IDEOGRAMS - 1 ));

  for my $group (@$chrorder_groups) {
    for my $tag_item ( @{ $group->{tags} } ) {
      my ($ideogram) = grep( ($_->{tag} !~ /__/ && $_->{tag} eq $tag_item->{tag}) || ($_->{tag} =~ /__/ && $_->{chr} eq $tag_item->{tag}), @IDEOGRAMS );
      if ($ideogram) {
	$display_idx_set->remove( $tag_item->{display_idx} ) if defined $tag_item->{display_idx};
	$allocated{ $ideogram->{idx} }++;
      }
    }
  }
  
  for my $group (@$chrorder_groups) {
    for my $tag_item ( @{ $group->{tags} } ) {
      my ($ideogram) = grep( ($_->{tag} !~ /__/ && $_->{tag} eq $tag_item->{tag}) || ($_->{tag} =~ /__/ && $_->{chr} eq $tag_item->{tag}), @IDEOGRAMS );
      #for my $ideogram ( grep( $_->{tag} eq $tag_item->{tag}, @IDEOGRAMS ) ) {
      if ( !$ideogram ) {
	my ($unallocated) = grep( ! exists $allocated{ $_->{idx} }, @IDEOGRAMS );
	$tag_item->{tag}          = $unallocated->{tag};
	$tag_item->{ideogram_idx} = $unallocated->{idx};
	$allocated{ $unallocated->{idx} }++;
	$display_idx_set->remove( $tag_item->{display_idx} );
      }
    }
  }

  for my $group (@$chrorder_groups) {
    for my $tag_item ( @{ $group->{tags} } ) {
      if ( defined $tag_item->{ideogram_idx} ) {
	my $display_idx;
	if ( !defined $tag_item->{display_idx} ) {
	  $display_idx = $display_idx_set->first;
	  $display_idx_set->remove($display_idx);
	  $tag_item->{display_idx} = $display_idx;
	} else {
	  $display_idx = $tag_item->{display_idx};
	}
	get_ideogram_by_idx( $tag_item->{ideogram_idx} )
	  ->{display_idx} = $display_idx
	    if defined $display_idx;
      } else {
	printwarning(
		     "trimming ideogram order - removing entry",
		     $tag_item->{group_idx},
		     "from group", $group->{idx}
		    );

	$tag_item->{display_idx} = undef;
      }
    }
  }

  for my $ideogram (@IDEOGRAMS) {
    if ( !defined $ideogram->{display_idx} ) {
      my $display_idx = $display_idx_set->first;
      $display_idx_set->remove($display_idx);
      $ideogram->{display_idx} = $display_idx;
    }
  }
  return $chrorder_groups;
}

# -------------------------------------------------------------------
sub reform_chrorder_groups {
  my $chrorder_groups = shift;
  my $reform_display_idx;
 REFORM:
  do {
    $reform_display_idx = 0;
    my $union = Set::IntSpan->new();

    for my $group (@$chrorder_groups) {
      my $set = Set::IntSpan->new();
      for my $tag_item ( @{ $group->{tags} } ) {
	$set->insert( $tag_item->{display_idx} );
      }

      $group->{display_idx_set} = $set;

      if ( 
	  !$union->intersect( $group->{display_idx_set} )->cardinality 
	 ) {
	$union = $union->union( $group->{display_idx_set} );
      } else {

	#printinfo("not adding group to union",$group->{idx});
	$reform_display_idx = 1;
	$group->{reform} = 1;
      }
    }

  GROUP:
    for my $group (@$chrorder_groups) {
      next unless $group->{reform};

      for my $start ( 0 .. @IDEOGRAMS - 1 - $group->{n} ) {
	my $newgroup =
	  map_set { $_ - $group->{display_idx_set}->min + $start }
	    $group->{display_idx_set};

	printdebug(
		   "test new set",                      "old",
		   $group->{display_idx_set}->run_list, "start",
		   $start,                              "new",
		   $newgroup->run_list,                 $union->run_list
		  );

	if ( !$newgroup->intersect($union)->cardinality ) {
	  printdebug( "found new set", $newgroup->run_list );
	  $union = $union->union($newgroup);
	  my @elements = $newgroup->elements;

	  for my $tag_item ( @{ $group->{tags} } ) {
	    $tag_item->{display_idx} = shift @elements;
	  }

	  $group->{display_idx_set} = $newgroup;
	  $group->{reform}          = 0;
	  next GROUP;
	}
      }

      if ( $group->{reform} ) {
	my @tags = map { $_->{tag} } @{ $group->{tags} };
	confess "fatal error - chromosomes_order string cannot be processed because group ",
	  join( $COMMA, @tags ), 
	    " cannot be placed in the display. This may be due to more tags in the chromosomes_order field than ideograms.";
      }
    }
  } while ($reform_display_idx);

  return $chrorder_groups;
}

# -------------------------------------------------------------------
sub parse_parameters {

  # Given a configuration file node (e.g. highlights), parse
  # parameter values, filtering for only those parameters that
  # are accepted for this node type
  #
  # parse_parameters( $CONF{highlights}, "highlights" );
  #
  # Parameters keyed by "default" in the list will be added to the
  # list of acceptable parameters for any type.
  #
  # If the $continue flag is set, then fatal errors are not triggered if
  # unsupported parameters are seen.
  #
  # parse_parameters( $CONF{highlights}, "highlights" , 1);
  #
  # Additional acceptable parameters can be added as a list.
  #
  # parse_parameters( $CONF{highlights}, "highlights" , 1, "param1",
  # "param2");
  
  my $node       = shift;
  my $type       = shift;
  my $continue   = shift;
  my @params     = @_;
  my %param_list = (
		    default => [ 
				qw(
				    url
				    id
				    record_limit perturb z show hide axis axis_color 
				    axis_thickness axis_spacing background background_color 
				    background_stroke_color background_stroke_thickness 
				    label_size label_offset label_font
				 ) 
			       ],
		    highlight => [
				  qw(
				      offset r0 r1 layer_with_data fill_color stroke_color
				      stroke_thickness ideogram minsize padding
				   )
				 ],
		    link => [
			     qw(
				 offset start end color flat rev reversed inv inverted twist 
				 thickness stroke_thickness stroke_color ribbon radius radius1 
				 radius2 bezier_radius crest bezier_radius_purity ribbon 
				 perturb_crest perturb_bezier_radius perturb_bezier_radius_purity
			      )
			    ],
		    connector => [qw(connector_dims thickness color r0 r1)],
		    plot      => [
				  qw(
				      angle_shift layers_overflow connector_dims extend_bin
				      label_rotate value scale_log_base layers_overflow_color
				      offset padding rpadding thickness layers margin max_gap
				      fill_color color thickness stroke_color stroke_thickness
				      orientation thickness r0 r1 glyph glyph_size min max
				      stroke_color stroke_thickness fill_under break_line_distance
				      type resolution padding resolve_order label_snuggle
				      snuggle_tolerance snuggle_link_overlap_test snuggle_sampling
				      snuggle_refine snuggle_link_overlap_tolerance
				      max_snuggle_distance resolve_tolerance sort_bin_values
				      link_thickness link_color show_links link_dims skip_run
				      min_value_change yoffset
				   )
				 ]
		   );

  $param_list{tile} = $param_list{plot};
  $param_list{text} = $param_list{plot};
  confess "parameter set of type [$type] is not defined"
    unless $param_list{$type};
  my $params;

  for my $key ( keys %$node ) {
    next if ref( $node->{$key} );
    my ( $key_root, $key_number ) = $key =~ /(.+?)(\d*)$/;

    if (
	grep( $key_root eq $_ || $key eq $_,
	      @{ $param_list{$type} },
	      @{ $param_list{default} }, @params )
       ) {
      if ( !defined $params->{$key} ) {
	my $value = $node->{$key};
	$value =~ s/;\S/,/g;
	$value = 1 if lc $value eq "yes";
	$value = 0 if lc $value eq "no";
	$params->{$key} = $value;
	next;
      } else {
	confess "parameter [$key] of type [$type] is defined twice";
      }
    }

    confess "parameter [$key] of type [$type] is not supported"
      unless $continue;
  }

  return $params;
}

# -------------------------------------------------------------------
sub text_size {
  validate(
	   @_,
	   {
            fontfile => 1,
            size     => 1,
            text     => 1,
	   }
	  );

  my %params = @_;
  my @bounds =
    GD::Image->stringFT( 0, $params{fontfile}, $params{size}, 0, 0, 0,
			 $params{text} );
  my ( $width, $height ) =
    ( abs( $bounds[2] - $bounds[0] + 1 ),
      abs( $bounds[5] - $bounds[1] + 1 ) );
  return ( $width, $height );
}

# -------------------------------------------------------------------
sub register_z_levels {
  # Examine a data set (e.g. all highlights, all plots) and enumerate
  # all the z values, which can be global, set-specific or data-specific.
  #
  # The list of z values is stored in the {param} tree of the global data
  # structure for highlights or plots
  #
  # DATA
  #   {highlights}{param}{zlist} = [ z1,z2,... ]
  #   {plots}     {param}{zlist} = [ z1,z2,... ]

  my $node = shift;
  my %z;
  $node->{param}{zlist}{0}++;
  $node->{param}{zlist}{ seek_parameter( "z", $node ) } = 1
    if defined seek_parameter( "z", $node );

  for my $dataset ( make_list( $node->{dataset} ) ) {
    if ( defined seek_parameter( "z", $dataset ) ) {
      $node->{param}{zlist}{ seek_parameter( "z", $dataset ) }++
    }

    for my $collection ( make_list( $dataset->{data} ) ) {
      if ( defined seek_parameter( "z", $collection ) ) {
	$node->{param}{zlist}{ seek_parameter( "z", $collection ) }++
      }

      for my $collection_point ( make_list( $collection->{data} ) ) {
	if ( defined seek_parameter( "z", $collection_point ) ) {
	  $node->{param}{zlist}
	    {
	      seek_parameter( "z", $collection_point ) }++
	    }
      }
    }
  }

  $node->{param}{zlist} = [ 
			   sort { $a <=> $b } keys %{ $node->{param}{zlist} } 
			  ];
}

# -------------------------------------------------------------------
sub unit_fetch {
  # Return a value's unit, with sanity checks. The unit fetch is the
  # basic unit access function and it should be the basis for any
  # other unit access wrappers. This is the only function that
  # checks against a list of acceptable units.
  #
  # Returns the value of units_nounit if the value has no unit
  # (i.e., bare number)
  #
  # Returns undef if the value string does not end in one of the
  # valid unit types
  #
  # If you just want to test the sanity of a value's format, call
  # unit_fetch in void context

  my $value = shift;
  my $param = shift;
  if ( !$CONF{units_ok} ) {
    confess "The parameter [$param] value of units_ok parameter is ",
      "not defined. Try setting it to units_ok=bupr";
  }

  if ( !$CONF{units_nounit} ) {
    confess "The parameter [$param] value of units_nounit parameter ",
      "is not defined. Try setting it to units_nounit=n";
  }

  if ( $value =~ /([$CONF{units_ok}])$/ ) {
    return $1;
  } elsif ( $value =~ /\d$/ ) {
    return $CONF{units_nounit};
  } else {
    confess
      "The parameter [$param] value [$value] is incorrectly formatted.";
  }
}

# -------------------------------------------------------------------
sub unit_validate {

  # Verify that a value's unit is one out of a provided list
  #
  # potential units are
  #
  # r : relative
  # p : pixel
  # u : chromosome unit (defined by chromosomes_unit parameter)
  # b : bases, or whatever your natural unit of distance is along the ideogram
  # n : no unit; value is expected to end in a digit
  #
  # If called without a list of acceptable units, unit_validate returns
  # the value if it is correctly formatted (i.e., an acceptable unit is found)
  # stripped of its unit

  my ( $value, $param, @unit ) = @_;
  croak "not units provided" unless @unit;

  # unit_fetch will die if $value isn't correctly formatted
  my $value_unit = unit_fetch( $value, $param );
  if ( grep( $_ eq $value_unit, @unit ) ) {
    return $value;
  } else {
    confess "The parameter [$param] value [$value] does not have ",
      "the correct unit [saw $value_unit], which should be one of ",
        join( $COMMA, @unit );
  }
}

# -------------------------------------------------------------------
sub unit_split {
  # Separate the unit from the value, and return the unit-less
  # number and the unit as a list
  my $value        = shift;
  my $param        = shift;
  my $unit         = unit_fetch( $value, $param );
  my $value_nounit = unit_strip( $value, $param );

  return ( $value_nounit, $unit );
}

# -------------------------------------------------------------------
sub unit_strip {
  # Remove the unit from a value and return the unit-less value
  my $value = shift;
  my $param = shift;
  my $unit  = unit_fetch($value);
  $value =~ s/$unit$//;

  return $value;
}

# -------------------------------------------------------------------
sub unit_test {
  # Verify that a unit is acceptable. If so, return the unit, otherwise
  # die.
  my $unit = shift;

  if ( $unit =~ /[$CONF{units_ok}]/ || $unit eq $CONF{units_nounit} ) {
    return $unit;
  } else {
    confess "Unit [$unit] fails format check.";
  }
}

# -------------------------------------------------------------------
sub unit_convert {
  # Convert a value from one unit to another.
  validate(
	   @_,
	   {
            from    => { type => SCALAR },
            to      => { type => SCALAR },
            factors => { type => HASHREF, optional => 1 },
	   }
	  );

  my %params = @_;
  my ( $value, $unit_from ) = unit_split( $params{from} );
  my $unit_to = unit_test( $params{to} );
  my $factors = $params{factors};

  if ( $factors->{ $unit_from . $unit_to } ) {
    return $value * $factors->{ $unit_from . $unit_to };
  } elsif ( $factors->{ $unit_to . $unit_from } ) {
    return $value * 1 / $factors->{ $unit_from . $unit_to };
  } elsif ( $unit_to eq $unit_from ) {
    return $value;
  } else {
    croak "cannot convert unit [$unit_from] to [$unit_to] - ",
      "no conversion factor supplied";
  }
}

# -------------------------------------------------------------------
sub unit_parse {
  # Parses a variable value that contains units. The value can be a single
  # value like
  #
  # 0.1r
  #
  # or an arithmetic expression
  #
  # TERM +/- TERM +/- TERM ...
  #
  # where TERM is one of
  #
  # 1. single value with any supported unit
  # 2. the string "dims(a,b)" for some parameters a,b

  my $expression = shift;
  my $ideogram   = shift;
  my $side       = shift;
  my $relative   = shift;

  my $radius_flag;
  if ( defined $side ) {
    if ( $side eq $DASH || !$side || $side =~ /inner/i ) {
      $radius_flag = "radius_inner";
    } elsif ( $side eq $PLUS_SIGN || $side == 1 || $side =~ /outer/i ) {
      $radius_flag = "radius_outer";
    }
  }

  if ($ideogram) {
    $expression =~ s/ideogram,/ideogram,$ideogram->{tag},/g;
  } else {
    $expression =~ s/ideogram,/ideogram,default,/g;
  }

  while ( $expression =~ /(dims\(([^\)]+)\))/g ) {
    my $string = $1;
    my $hash   = "\$" . $string;
    my @args   = split( $COMMA, $2 );

    #printinfo("dims",$string,"args",@args);
    $hash = sprintf( "\$DIMS->%s",
		     join( $EMPTY_STR, map { sprintf( "{'%s'}", $_ ) } @args ) );

    #printdumper($DIMS->{ideogram}{default});
    my $hash_value = eval $hash;
    confess "dimension [$hash] is not defined in expression $expression"
      if !defined $hash_value;
    $expression =~ s/\Q$string\E/$hash_value/g;
  }

  while ( $expression =~ /([\d\.]+[$CONF{units_ok}])/g ) {
    my $string = $1;
    my ( $value, $unit ) = unit_split($string);
    my $value_converted;

    if ( $unit eq "u" ) {

      # convert from chromosome units to bases
      $value_converted = unit_convert(
				      from    => $string,
				      to      => "b",
				      factors => { ub => $CONF{chromosomes_units} }
				     );
    } else {

      # convert from relative or pixel to pixel
      my $rpfactor;
      my $tag = $ideogram ? $ideogram->{tag} : "default";

      if ( $value < 1 ) {
	$rpfactor = $relative
	  || $DIMS->{ideogram}{$tag}{ $radius_flag || "radius_inner" };
      } else {
	$rpfactor = $relative
	  || $DIMS->{ideogram}{$tag}{ $radius_flag || "radius_outer" };
      }
      $value_converted = unit_convert(
				      from    => $string,
				      to      => "p",
				      factors => { rp => $rpfactor }
				     );
    }

    $expression =~ s/$string/$value_converted/;
  }

  $expression = eval $expression;

  return $expression;
}

# -------------------------------------------------------------------
sub draw_axis_break {
  my $ideogram      = shift;
  my $ideogram_next = $ideogram->{next};
  return unless $CONF{ideogram}{spacing}{axis_break};
  my $style_id   = $CONF{ideogram}{spacing}{axis_break_style};
  my $style_data = $CONF{ideogram}{spacing}{break_style}{$style_id};
  my $radius_change =
    $DIMS->{ideogram}{ $ideogram->{tag} }{radius} !=
      $DIMS->{ideogram}{ $ideogram_next->{tag} }{radius};

  my $thickness = unit_convert(
			       from => unit_validate(
						     seek_parameter( "thickness", $style_data ),
						     "ideogram/spacing/break_style/thickness",
						     qw(r p)
						    ),
			       to      => "p",
			       factors => { rp => $ideogram->{thickness} }
			      );

  if ( $style_id == 1 ) {
    # slice connecting the IDEOGRAMS
    if ( $ideogram->{break}{start} && $ideogram->{prev}{chr} ne $ideogram->{chr}) {
      draw_break(
		 {
		  chr      => $ideogram->{chr},
		  ideogram => $ideogram,
		  #start_offset => ideogram_spacing( $ideogram, $ideogram->{prev} ) / 2,
		  start_offset => ideogram_spacing_helper( $ideogram->{break}{start}),
		  start      => $ideogram->{set}->min,
		  end        => $ideogram->{set}->min,
		  fillcolor  => $style_data->{fill_color},
		  thickness  => $thickness,
		  style_data => $style_data
		 }
		);
    }

    if ($ideogram->{break}{end} && $ideogram->{next}{chr} ne $ideogram->{chr}) {
      draw_break(
		 {
		  chr      => $ideogram->{chr},
		  ideogram => $ideogram,
		  start    => $ideogram->{set}->max,
		  #end_offset => ideogram_spacing( $ideogram, $ideogram->{next} ) / 2,
		  end_offset => ideogram_spacing_helper( $ideogram->{break}{end}),
		  end        => $ideogram->{set}->max,
		  fillcolor  => $style_data->{fill_color},
		  thickness  => $thickness,
		  style_data => $style_data
		 }
		);
    }
    if ( $ideogram->{chr} eq $ideogram->{next}{chr} ) {
      if ($radius_change) {
	draw_break(
		   {
		    chr      => $ideogram->{chr},
		    ideogram => $ideogram,
		    start    => $ideogram->{set}->max,
		    end      => $ideogram_next->{set}->min,
		    #end_offset => -ideogram_spacing( $ideogram, $ideogram_next ) / 2,
		    end_offset => -ideogram_spacing_helper($ideogram->{break}{end}),
		    fillcolor  => $style_data->{fill_color},
		    thickness  => $thickness,
		    style_data => $style_data
		   }
		  );
	draw_break(
		   {
		    chr      => $ideogram->{chr},
		    ideogram => $ideogram_next,
		    start    => $ideogram->{set}->max,
		    end      => $ideogram_next->{set}->min,
		    #start_offset => -ideogram_spacing( $ideogram, $ideogram_next ) / 2,
		    start_offset => -ideogram_spacing_helper( $ideogram->{break}{start}),
		    fillcolor  => $style_data->{fill_color},
		    thickness  => $thickness,
		    style_data => $style_data
		   }
		  );
      } else {
	draw_break(
		   {
		    chr        => $ideogram->{chr},
		    ideogram   => $ideogram,
		    start      => $ideogram->{set}->max,
		    end        => $ideogram_next->{set}->min,
		    fillcolor  => $style_data->{fill_color},
		    thickness  => $thickness,
		    style_data => $style_data
		   }
		  );
      }
    }
  } elsif ( $style_id == 2 ) {
    # two radial break lines
    if ($ideogram->{break}{start} && $ideogram->{prev}{chr} ne $ideogram->{chr} ) {
      draw_break(
		 {
		  chr        => $ideogram->{chr},
		  ideogram   => $ideogram,
		  start      => $ideogram->{set}->min,
		  end        => $ideogram->{set}->min,
		  thickness  => $thickness,
		  style_data => $style_data
		 }
		);

      draw_break(
		 {
		  chr          => $ideogram->{chr},
		  ideogram     => $ideogram,
		  start_offset => ideogram_spacing_helper($ideogram->{break}{start}),
		  end_offset   => -ideogram_spacing_helper($ideogram->{break}{start}),
		  start        => $ideogram->{set}->min,
		  end          => $ideogram->{set}->min,
		  thickness    => $thickness,
		  style_data   => $style_data
		 }
		);
    }
    if ($ideogram->{break}{end} && $ideogram->{next}{chr} ne $ideogram->{chr}) {
      draw_break(
		 {
		  chr        => $ideogram->{chr},
		  ideogram   => $ideogram,
		  start      => $ideogram->{set}->max,
		  end        => $ideogram->{set}->max,
		  thickness  => $thickness,
		  style_data => $style_data
		 }
		);
      draw_break(
		 {
		  chr          => $ideogram->{chr},
		  ideogram     => $ideogram,
		  start_offset => -ideogram_spacing_helper($ideogram->{break}{end}),
		  end_offset   => ideogram_spacing_helper($ideogram->{break}{end}),
		  start        => $ideogram->{set}->max,
		  end          => $ideogram->{set}->max,
		  thickness    => $thickness,
		  style_data   => $style_data
		 }
		);
    }
    if ( $ideogram->{next}{chr} eq $ideogram->{chr} ) {
      draw_break(
		 {
		  chr        => $ideogram->{chr},
		  ideogram   => $ideogram,
		  start      => $ideogram->{set}->max,
		  end        => $ideogram->{set}->max,
		  thickness  => $thickness,
		  style_data => $style_data
		 }
		);
      draw_break(
		 {
		  chr        => $ideogram->{next}{chr},
		  ideogram   => $ideogram_next,
		  start      => $ideogram->{next}{set}->min,
		  end        => $ideogram->{next}{set}->min,
		  thickness  => $thickness,
		  style_data => $style_data
		 }
		);
    }
  }
}

# -------------------------------------------------------------------
sub draw_break {
  my $args          = shift;
  my $ideogram      = $args->{ideogram};
  my $ideogram_next = $args->{ideogram}{next};
  my $style_data    = $args->{style_data};

  slice(
        image        => $IM,
        chr          => $args->{chr},
        start        => $args->{start},
        end          => $args->{end},
        start_offset => $args->{start_offset},
        end_offset   => $args->{end_offset},
        fillcolor    => $args->{fillcolor},
        radius_from => $DIMS->{ideogram}{ $ideogram->{tag} }{radius_outer} -
	$DIMS->{ideogram}{ $ideogram->{tag} }{thickness} / 2 -
	$args->{thickness} / 2,
        radius_to => $DIMS->{ideogram}{ $ideogram->{tag} }{radius_outer} -
	$DIMS->{ideogram}{ $ideogram->{tag} }{thickness} / 2 +
	$args->{thickness} / 2,
        edgecolor  => $style_data->{stroke_color},
        edgestroke => $style_data->{stroke_thickness},
       );
}

# -------------------------------------------------------------------
sub init_brush {
  my ( $w, $h, $brush_color ) = @_;
  $h ||= $w;
  my $brush;

  eval { $brush = GD::Image->new( $w, $h, $CONF{"24bit"} ); };

  if ($@) {
    $brush = GD::Image->new( $w, $h );
  }

  my $color = allocate_colors($brush);

  if ( $brush_color && $color->{$brush_color} ) {
    $brush->fill( 0, 0, $color->{$brush_color} );
  }

  return ( $brush, $color );
}

# -------------------------------------------------------------------
sub read_data_file {
  # read a coordinate data file and associated options
  #
  # for each data type, the format is
  #
  # chr start end options
  #
  # where the options string is of the form
  #
  # var1=value1,var2=value2,...
  #
  # For data values which are single-coordinates (e.g. data tracks)
  # the end coordinate should be set to "-" and isn't parsed
  #
  # v0.48 - if min>max, then the data point is tagged with rev=>1
  my ( $file, $type, $options ) = @_;

  open( F, $file ) || confess "cannot open data file [$file]";

  my $fields = {
		highlight => [qw(chr start end options)],
		link      => [qw(id chr start end options)],
		plot      => [qw(chr start end value options)],
		connector => [qw(chr start end options)],
		text      => [qw(chr start end label options)],
		tile      => [qw(chr start end options)],
	       };

  my $rx = {
	    start   => qr/^[-+]?[0-9]*\.?[0-9]+([eE][-+]?[0-9]+)?$/,
	    end     => qr/^[-+]?[0-9]*\.?[0-9]+([eE][-+]?[0-9]+)?$/,
	    value   => qr/^[\d+-.Ee,]+$/,
	    label   => qr/^.+/,
	    options => qr/=/
	   };

  my ( $data, $recnum, $prev_value );

 LINE:
  while (<F>) {
    chomp;
    next if /^\s*#/;
    next if /^\s*$/;
    my @tok   = $CONF{file_delim} ? split($CONF{file_delim}) : split;
    my $datum = {};
    my $fail;
    for my $i ( 0 .. @{ $fields->{$type} } - 1 ) {
      my $field = $fields->{$type}[$i];
      next if $field eq $DASH;
      my $value = $tok[$i];
      if ( $rx->{$field} && $value && $value !~ /$rx->{$field}/ ) {
	warn "data field [$field] value [$value] does not pass ",
	  "filter [$rx->{$field}]";
	$fail = 1;
	next;
      }
      if ( $field eq "options" ) {
	my @params = split(/,/,$value);
	my %params;
	for my $param ( @params ) {
	  #printinfo("paraminfo",$param);
	  if($param =~ /^([^=]+)=(.+)$/) {
	    $params{$1} = $2;
	  }
	}
	my $params = parse_parameters( \%params, $type );
	$datum->{param} = $params if $params;
      } else {
	$datum->{data}{$field} = $value;
      }

      if ( $field eq "value" ) {
	if (   $options->{min_value_change}
	       && defined $prev_value
	       && abs( $value - $prev_value ) <
	       $options->{min_value_change}
	   ) {
	  next LINE;
	}

	if (   $options->{skip_run}
	       && defined $prev_value
	       && $field eq "value"
	       && $value eq $prev_value 
	   ) {
	  next LINE;
	}
      }
    }

    $prev_value = $datum->{data}{value};
    $datum->{param} ||= {};

    #
    # data points that filed a regex check against values are skipped
    #
    next if $fail;

    #
    # if the start/end values are reversed, i.e. end<start, then
    # swap them and set rev flag
    #
    if ( $type eq "link" ) {
      if ( $datum->{data}{start} > $datum->{data}{end} ) {
	@{ $datum->{data} }{qw(start end)} =
	  @{ $datum->{data} }{qw(end start)};
	$datum->{data}{rev} = 1;
      } elsif ($datum->{param}{rev}
	       || $datum->{param}{reverse}
	       || $datum->{param}{inv}
	       || $datum->{param}{inverted} 
	      ) {
	$datum->{data}{rev} = 1;
      } else {
	$datum->{data}{rev} = 0;
      }
    }

    #
    # coordinate sanity check
    #
    if (   defined $datum->{data}{start}
	   && defined $datum->{data}{end}
	   && $datum->{data}{start} > $datum->{data}{end} 
       ) {
      if ( $type ne "connector" ) {
	confess "error - input data line in file [$file] for ",
	  "type [$type] has start position [$datum->{data}{start}] ",
	    "greater than end position [$datum->{data}{end}]";
      }
    }

    # if padding is required, expand the coordinate
    if ( $datum->{param}{padding} ) {
      if ( $datum->{data}{start} ) {
	$datum->{data}{start} -= $datum->{param}{padding};
      }

      if ( $datum->{data}{end} ) {
	$datum->{data}{end} += $datum->{param}{padding};
      }
    }

    #
    # if the minsize parameter is set, then the coordinate span is
    # expanded to be at least this value
    #
    if (   $datum->{param}{minsize}
	   && $datum->{data}{end} - $datum->{data}{start} <
	   $datum->{param}{minsize}
       ) {
      my $size   = $datum->{data}{end} - $datum->{data}{start} + 1;
      my $makeup = $datum->{param}{minsize} - $size;

      $datum->{data}{start} -= $makeup / 2;
      $datum->{data}{end}   += $makeup / 2;

      if ( $datum->{data}{start} < 0 ) {
	$datum->{data}{start} = 0;
	$datum->{data}{end}   = $datum->{param}{minsize} - 1;
      }
    }

    # if a set structure was requested, make it
    if ( $options->{addset} ) {
      if ( $datum->{data}{start} != $datum->{data}{end} ) {
	$datum->{data}{set} = Set::IntSpan->new(
						sprintf( "%d-%d", @{ $datum->{data} }{qw(start end)} ) );
      } else {
	$datum->{data}{set} =
	  Set::IntSpan->new( $datum->{data}{start} );
      }
    }

    if ($datum) {
      if ( defined $options->{keyby} || defined $options->{groupby} ) {
	my $key =
	  $datum->{data}{ $options->{keyby} || $options->{groupby} };

	if (   !exists $data->{$key}
	       && $options->{record_limit}
	       && int( keys %$data ) >= $options->{record_limit} 
	   ) {
	  last;
	}

	push @{ $data->{$key}{data} }, $datum;
      } else {
	last
	  if $options->{record_limit}
	    && $data
	      && @{$data} >= $options->{record_limit};

	#
	# for stacked histograms where values are comma separated
	#
	if ( $datum->{data}{value} =~ /,/ ) {
	  my @values = split( /,/, $datum->{data}{value} );
	  my ( @values_sorted, @values_idx_sorted );

	  if ( $options->{sort_bin_values} ) {
	    @values_sorted = sort { $b <=> $a } @values;
	    @values_idx_sorted =
	      map  { $_->[0] }
		sort { $b->[1] <=> $a->[1] }
		  map  { [ $_, $values[$_] ] } ( 0 .. @values - 1 );
	  } else {
	    @values_sorted     = @values;
	    @values_idx_sorted = ( 0 .. @values - 1 );
	  }

	  for my $i ( 0 .. @values - 1 ) {
	    my $z         = $i;
	    my $cumulsum  = sum( @values_sorted[ 0 .. $i ] );
	    my $thisdatum = dclone($datum);

	    #printdumper($thisdatum);

	    $thisdatum->{data}{value} = $cumulsum;
	    $thisdatum->{param}{z}    = $z;

	    if ( $options->{param} ) {
	      for my $param ( keys %{ $options->{param} } ) {
		my @param_values = split(
					 /,/,
					 (
					  $datum->{param}{$param}
                                          || $options->{param}{$param}
					 )
					);
		next unless @param_values;
		my $param_value =
		  $param_values[ $values_idx_sorted[$i]
				 % @param_values ];
		$thisdatum->{param}{$param} = $param_value;
	      }
	    }

	    push @{$data}, {
                            param => $thisdatum->{param},
                            data  => [$thisdatum]
			   };
	  }
	} else {
	  push @{$data}, {
			  param => $datum->{param},
			  data  => [$datum]
			 };
	}
      }
    }
  }

  if ( defined $options->{groupby} ) {
    my $data_new;

    for my $key ( keys %$data ) {
      push @{$data_new}, { data => $data->{$key}{data}, param => {} };
    }
    return $data_new;
  } else {
    return $data;
  }
}

# -------------------------------------------------------------------
sub draw_ticks {
  # draw ticks and associated labels

  validate( @_, { ideogram         => 1 } );

  my %args             = @_;
  my $ideogram         = $args{'ideogram'};
  my $chr              = $ideogram->{chr};

  my @requested_ticks = make_list( $CONF{ticks}{tick} );

  ################################################################
  # Identify ideograms on which ticks should be drawn. By default, ticks
  # are drawn on each ideogram (chromosomes_display_default=yes). To suppress
  # ticks, use
  #
  # chromosomes = -hs1;-hs2 ...
  # 
  # To draw only on specific ideograms, set chromosomes_display_default=no
  # and define
  #
  # chromosomes = hs1;hs5;...
  #
  # Tick blocks can have these parameters defined, which will override
  # their definition in <ticks> for the tick block.
  #
  # To show (or suppress) ticks within a range, 
  #
  # chromosomes = hs1:10-20
  # chromosomes = -hs1:10-20
  #

  for my $tick (@requested_ticks) {
    next if defined $tick->{_ideogram};
    
    my $show_default    = seek_parameter( "chromosomes_display_default", $tick, $CONF{ticks} )
      || ! defined seek_parameter( "chromosomes_display_default", $tick, $CONF{ticks} );
    my $ideogram_filter = seek_parameter( "chromosomes", $tick, $CONF{ticks} );
    $tick->{_ideogram} = {show_default=>$show_default,
			  filter=>merge_ideogram_filters(parse_ideogram_filter(seek_parameter( "chromosomes", $CONF{ticks} )),
							 parse_ideogram_filter(seek_parameter( "chromosomes", $tick )))
			 };
  }

  # parse and fill data structure for each tick level - process
  # units on grids and spacing (do this now rather than later when
  # ticks are drawn)

  for my $tick (@requested_ticks) {
    # do not process this tick if it is not being shown
    next if !show_element($tick);
    process_tick_structure( $tick, $ideogram );
  }

  # keep track of whether ticks have been drawn at a given radius
  my %pos_ticked;

  my $max_tick_length = max( map { $_->{size} } @requested_ticks );
  $DIMS->{tick}{max_tick_length} = $max_tick_length;

  my @ticks;
  my $tick_groups;

  # ticks with relative spacing have had their spacing already
  # defined (rspacing*ideogram_size) by process_tick_structure()
  for my $tickdata ( sort { $b->{spacing} <=> $a->{spacing} } @requested_ticks ) {
    next unless show_element($tickdata);
    my $tick_label_max;
    for my $tick_radius ( @{ $tickdata->{_radius} } ) {
      printinfo(
                "drawing ticks",
                $chr,
                "radius",
                $tick_radius,
                "type",
                $tickdata->{spacing_type} || "absolute",
                "spacing",
                $tickdata->{spacing_type} =~ /rel/
                ? $tickdata->{rspacing}
                : $tickdata->{spacing}
	       );
      my @mb_pos;
      #
      # the absolute start and end tick positions will be Math::BigFloat;
      #
      my $dims_key;
      if ( seek_parameter( "spacing", $tickdata, $CONF{ticks} ) ) {
	$dims_key = join( $COLON, $tickdata->{spacing}, $tick_radius );
	my ( $mb_pos_start, $mb_pos_end );
	if ( seek_parameter( "spacing_type", $tickdata, $CONF{ticks} ) eq "relative" ) {
	  if ( seek_parameter("rdivisor|label_rdivisor", $tickdata, $CONF{ticks} ) eq "ideogram" ) {
	    # IDEOGRAM RELATIVE
	    # the start/end position will be the start-end range of this ideogram
	    # i.e. - relative positions will start at the start of ideogram crop, relative to chr length
	    $mb_pos_start = Math::BigFloat->new( $ideogram->{set}->min );
	    $mb_pos_end   = $ideogram->{set}->max + 1;
	  } else {
	    # CHROMOSOME RELATIVE
	    # the start/end position will be the 0-chrlen for this ideogram
	    # i.e. - relative positions will start at 0 
	    $mb_pos_start = Math::BigFloat->new(0);
	    $mb_pos_end   = $ideogram->{chrlength} - 1;
	  }
	} else {
	  $mb_pos_start = nearest( $tickdata->{spacing}, $ideogram->{set}->min );
	  $mb_pos_end   = nearest( $tickdata->{spacing}, $ideogram->{set}->max );
	}

	# printinfo("mbpos","start",$mb_pos_start,"end",$mb_pos_end);

	#
	# compile a list of position for this tick - this is an important step because we will
	# draw positions from this list and not from the tick data structures
	#
	for ( my $mb_pos = $mb_pos_start ; $mb_pos <= $mb_pos_end ; $mb_pos += $tickdata->{spacing} ) {
	  push @mb_pos, $mb_pos;
	}
      } elsif ( seek_parameter( "position", $tickdata, $CONF{ticks} ) ) {
	$dims_key = join( $COLON, join( $EMPTY_STR, @{ $tickdata->{position} } ), $tick_radius );
	@mb_pos = sort {$a <=> $b} @{ $tickdata->{position} };
      }

      # go through every position and draw the tick

      for my $mb_pos (@mb_pos) {
	# if the tick is outside the ideogram, it isn't shown
	next if !$ideogram->{set}->member($mb_pos);

	my $pos = $mb_pos;
	my $do_not_draw;
	if ( ! seek_parameter( "force_display", $tickdata, $CONF{ticks} ) ) {
	  #
	  # Normally, if a tick at a given radius and position has
	  # been drawn, it is not drawn again (e.g. 10 Mb ticks are
	  # not drawn on top of 100 Mb ticks)
	  #
	  # However, you can set force_display=yes to insist that a
	  # tick be displayed, even if there is another tick at this
	  # position from a different spacing (e.g. force display of
	  # 10Mb tick even if 100Mb tick at this angular position has
	  # been drawn). This is useful only if the radial distance is
	  # different for these ticks, or if a mixture of
	  # relative/absolute spacing/labeling is being used.
	  #
	  # The only exception to this is when a tick is used to define
	  # an image map. In this case, the process plays out but the
	  # actual tick is not drawn (but the loop is used to generate
	  # the image map element).
	  $do_not_draw = $pos_ticked{$tick_radius}{$pos}++;
	  #next if $do_not_draw && ! $tickdata->{url};
	}

	# determine whether this tick is suppressed by 'chromosomes_display_default'
	# and 'chromosomes' parameters, which were parsed using parse_ideogram_filter()
	my $is_suppressed = 0;
	my $tag = $ideogram->{tag};
	#printdumper($tickdata->{_ideogram});
	if($tickdata->{_ideogram}{show_default} ) {
	  # This tick will be shown on all chromosomes by default. Check
	  # check whether this position is explicitly excluded.
	  if(defined $tickdata->{_ideogram}{filter}{$tag}{hide}
	     &&
	     $tickdata->{_ideogram}{filter}{$tag}{hide}->member($pos)) {
	    $is_suppressed = 1;
	  }
	} else {
	  # This tick is not shown by default. Check that its combined
	  # filter (show-hide) contains this position
	  if(defined $tickdata->{_ideogram}{filter}{$tag}{combined}
	     &&
	     $tickdata->{_ideogram}{filter}{$tag}{combined}->member($pos)) {
	    $is_suppressed = 0;
	  } else {
	    $is_suppressed = 1;
	  }
	}
	next if $is_suppressed;

	# TODO - fix/handle this - is it necessary?
	# this is a bit of a hack, but is required because we
	# use 0-indexed positions on the ideograms, but a
	# relative tick mark at 1.0 won't be shown because it
	# will be +1 past the end of the ideogram
	#
	if (seek_parameter( "spacing_type", $tickdata, $CONF{ticks} ) eq "relative" ) {
	  #$pos-- if $mb_pos > $mb_pos[0];
	}

	# 
	# Turn $pos into a normal string, from Math::BigFloat
	# 

	$pos = $pos->bstr if ref($pos) eq "Math::BigFloat";

	my $tick_angle = getanglepos( $pos, $chr );
	my $this_tick_radius = $tick_radius +
	  unit_parse( ( $tickdata->{offset} || 0 ), $ideogram, undef, $ideogram->{thickness} ) +
	    unit_parse( ( $CONF{ticks}{offset} || 0 ), $ideogram, undef, $ideogram->{thickness} );

	# calculate the distance across a neighbourhood of 2*pix_sep_n+1 ticks
	# determine from this the average tick-to-tick distance (use multiple ticks for
	# the calculation to cope with local scale adjustments).
	my $tick_color;
	if (defined seek_parameter("tick_separation", $tickdata, $CONF{ticks})
	    && $tickdata->{spacing}) {
	  my $pix_sep_n = 2;
	  my @pix_sep   = ();
	  for my $i ( -$pix_sep_n .. $pix_sep_n-1 ) {
	    next if 
	      ! $ideogram->{set}->member( $pos + $tickdata->{spacing}*$i )
		||
		  ! $ideogram->{set}->member( $pos + $tickdata->{spacing}*($i+1) );
	    my $d = $this_tick_radius*$DEG2RAD*abs(getanglepos($pos+$tickdata->{spacing}*$i,$chr)
						   -
						   getanglepos($pos+$tickdata->{spacing}*($i+1),$chr));
	    push @pix_sep, $d;
	  }
	  my $pix_sep = average(@pix_sep);
	  $tickdata->{pix_sep} = $pix_sep;
	  # determine whether to draw the tick based on requirement of minimum tick separation, if defined
	  my $min_sep = unit_strip(unit_validate(seek_parameter("tick_separation", $tickdata, $CONF{ticks}),
						 "ticks/tick/tick_separation",
						 "p"
						));
	  # don't draw this tick - move to next one
	  if($pix_sep < $min_sep) {
	    $tick_color = "red";
	    next;
	  }
	}

	# distance to closest ideogram edge
	my $edge_d_start = $this_tick_radius*$DEG2RAD*abs($tick_angle-getanglepos($ideogram->{set}->min,$chr));
	my $edge_d_end   = $this_tick_radius*$DEG2RAD*abs($tick_angle-getanglepos($ideogram->{set}->max,$chr));
	my $edge_d_min   = int( min( $edge_d_start, $edge_d_end ) );

	if (my $edge_d = seek_parameter( "min_distance_to_edge", $tickdata, $CONF{ticks} ) ) {
	  $edge_d = unit_strip(unit_validate($edge_d,
					     "ticks/tick/min_distance_to_edge",
					     "p"
					    ));
	  next if $edge_d_min < $edge_d;
	}

	debug_or_group("ticks") && printdebug(
					      "tick",
					      $chr,
					      "tick_spacing",
					      $tickdata->{spacing},
					      "tick_radius",
					      $this_tick_radius,
					      "tick_angle",
					      sprintf( "%.1f", $tick_angle ),
					      "textangle",
					      sprintf( "%.1f", textangle($tick_angle) ),
					      "d_tick",
					      sprintf("%.3f",$tickdata->{pix_sep}),
					      "d_edge",
					      $edge_d_min,
					      "thickness",
					      $DIMS->{tick}{ $tickdata->{dims_key} }{thickness},
					      "size",
					      $DIMS->{tick}{ $tickdata->{dims_key} }{size},
					     );

	my $start_a = getanglepos( $pos, $chr );

	#
	# register the tick for drawing
	#

	my ( $r0, $r1 );
	if ( seek_parameter( "orientation", $tickdata, $CONF{ticks} ) eq "in" ) {
	  $r0 = $this_tick_radius - $DIMS->{tick}{$dims_key}{size};
	  $r1 = $this_tick_radius;
	} else {
	  $r0 = $this_tick_radius;
	  $r1 = $this_tick_radius + $DIMS->{tick}{$dims_key}{size};
	}

	my $tick_group_entry = {
				do_not_draw => $do_not_draw,
				tickdata    => $tickdata,
				color       => $tick_color,
				r0          => $r0,
				r1          => $r1,
				a           => $tick_angle,
				pos         => $pos,
				coordinates => [getxypos( $tick_angle, $r0 ),
						getxypos( $tick_angle, $r1 )],
			       };
	
	#
	# now check whether we want to draw the label, and if
	# so, add the label data to the tick's registration in
	# @ticks
	#

	if ( $CONF{show_tick_labels}
	     && seek_parameter( "show_label", $tickdata, $CONF{ticks} )
	     && $edge_d_min >= $DIMS->{tick}{$dims_key}{min_label_distance_to_edge} ) {
	  my $tick_label;
	  my $multiplier  = unit_parse(seek_parameter("multiplier|label_multiplier", $tickdata, $CONF{ticks} ) ) || 1;
	  my $rmultiplier = unit_parse(seek_parameter("rmultiplier|label_rmultiplier", $tickdata, $CONF{ticks})) || 1;
	  #
	  # position, relative to ideogram size, or chromosome size, as requested by
	  #
	  my $pos_relative;
	  if (seek_parameter("rdivisor|label_rdivisor", $tickdata, $CONF{ticks}) eq "ideogram" ) {
	    $pos_relative = $mb_pos - $ideogram->{set}->min;
	    $pos_relative /= ( $ideogram->{set}->cardinality );
	  } else {
	    $pos_relative = $mb_pos / $ideogram->{chrlength};
	  }

	  # do we want a relative label? (e.g. 0.3 instead of 25?)
	  my $label_relative = seek_parameter( "label_relative", $tickdata, $CONF{ticks} );
	  my $precision = 0.001;
	  if ( defined seek_parameter( "mod", $tickdata, $CONF{ticks} ) ) {
	    my $mod = unit_parse(seek_parameter( "mod", $tickdata, $CONF{ticks} ) );
	    $pos_relative = ( $mb_pos % $mod ) / $mod;
	    if ($label_relative) {
	      $tick_label = sprintf(seek_parameter("format", $tickdata, $CONF{ticks}),
				    $pos_relative * $rmultiplier);
	    } else {
	      $tick_label = sprintf(seek_parameter("format", $tickdata, $CONF{ticks}),
				    ( $mb_pos % $mod ) * $multiplier );
	    }
	  } else {
	    if ($label_relative) {
	      $tick_label = sprintf(seek_parameter("format", $tickdata, $CONF{ticks}),
				    $pos_relative * $rmultiplier);
	    } else {
	      $tick_label = sprintf(seek_parameter("format", $tickdata, $CONF{ticks}),
				    $mb_pos * $multiplier);
	    }
	  }

	  if (defined seek_parameter("thousands_sep|thousands_separator", $tickdata,$CONF{ticks})) {
	    $tick_label = add_thousands_separator($tick_label);
	  }
	  if (defined seek_parameter( "suffix", $tickdata, $CONF{ticks} ) ) {
	    $tick_label .= seek_parameter( "suffix", $tickdata, $CONF{ticks} );
	  }
	  if (defined seek_parameter( "prefix", $tickdata, $CONF{ticks} )) {
	    $tick_label = seek_parameter( "prefix", $tickdata, $CONF{ticks} ) . $tick_label;
	  }
	  $tick_label = seek_parameter( "label", $tickdata ) if defined seek_parameter( "label", $tickdata );
	  my $tickfont     = seek_parameter( "tick_label_font", $tickdata, $CONF{ticks} ) || "default";
	  my $tickfontfile = locate_file(file => $CONF{fonts}{ $tickfont } );
	  my $label_size   = unit_convert(from => unit_validate(seek_parameter("label_size", $tickdata, $CONF{ticks}),
								"ticks/tick/label_size",
								qw(p r)
							       ),
					  to      => "p",
					  factors => { rp => $DIMS->{tick}{$dims_key}{size} });
	  my @label_bounds = label_bounds($tickfontfile,$label_size,$tick_label);#$GD::Image->stringFT( $COLORS->{black}, $tickfontfile, $label_size, 0, 0, 0, $tick_label );
	  my ( $label_width, $label_height ) = text_label_size(@label_bounds);

	  my $label_offset;
	  if ( my $offset =  seek_parameter( "label_offset", $CONF{ticks} )) {
	    $label_offset += unit_parse( $offset, $ideogram, undef, $DIMS->{tick}{$dims_key}{size} );
	  }
	  if ( my $offset = seek_parameter( "label_offset", $tickdata )) {
	    $label_offset += unit_parse( $offset, $ideogram, undef, $DIMS->{tick}{$dims_key}{size} );
	  }

	  #
	  # label offset is no longer cumulative v0.47 Unless
	  # individual offset values are applied, distance of tick
	  # label to tick radius is based on the longest tick
	  # (max_tick_length).  The label_offset parameter is used
	  # to adjust label position.
	  #

	  my $tick_label_radius;
	  if (seek_parameter( "orientation", $tickdata,$CONF{ticks} ) eq "in") {
	    $tick_label_radius = $tick_group_entry->{r0} - $label_offset - $label_width; # - $max_tick_length
	  } else {
	    $tick_label_radius = $tick_group_entry->{r1} + $label_offset; # + $max_tick_length
	  }

	  my ( $offset_angle, $offset_radius ) =
	    textoffset( getanglepos( $pos, $chr ),
			$tick_label_radius, $label_width, $label_height );

	  debug_or_group("ticks") && printdebug(
						"ticklabel",
						$tick_label,
						"tickpos",
						$pos,
						"angle",
						$tick_angle + $offset_angle,
						"radius",
						$tick_label_radius + $offset_radius,
						"offseta",
						$offset_angle,
						"offsetr",
						$offset_radius,
						"params",
						getanglepos( $pos, $chr ),
						$tick_label_radius,
						$label_width,
						$label_height
					       );

	  $tick_group_entry->{labeldata} = {
					    label_separation => seek_parameter("label_separation", $tickdata, $CONF{ticks}),
					    font   => $tickfontfile,
					    color  => seek_parameter("label_color|color", $tickdata,$CONF{ticks}),
					    size   => $label_size,
					    pangle => $tick_angle, # + $offset_angle,
					    radius => $tick_label_radius + $offset_radius,
					    angle  => $DEG2RAD * textangle($tick_angle),
					    xy     => [getxypos($tick_angle + $offset_angle,
								$tick_label_radius + $offset_radius)],
					    svgxy => [getxypos($tick_angle + $offset_angle / $CONF{svg_font_scale},
							       $tick_label_radius
							      )],
					    svgangle => textanglesvg($tick_angle),
					    text     => $tick_label,
					    chr      => $chr,
					    start    => $pos,
					    end      => $pos,
					    start_a  => $tick_radius*$tick_angle*$DEG2RAD - $label_height / 2,
					    end_a    => $tick_radius*$tick_angle*$DEG2RAD + $label_height / 2,
					   };
	}
	
	if ( $CONF{show_grid} ) {
	  if ( $tickdata->{grid} ) {
	    my $grid_r1 = unit_parse(seek_parameter("grid_start", $tickdata, $CONF{ticks}, \%CONF),$ideogram);
	    my $grid_r2 = unit_parse(seek_parameter("grid_end",   $tickdata, $CONF{ticks}, \%CONF),$ideogram);
	    $tick_group_entry->{griddata}{coordinates} = [getxypos( $start_a, $grid_r1 ),
							  getxypos( $start_a, $grid_r2 )];
	    $tick_group_entry->{griddata}{r0} = $grid_r1;
	    $tick_group_entry->{griddata}{r1} = $grid_r2;
	  }
	}
	push @ticks, $tick_group_entry;
	push @{$tick_groups->{ $tickdata->{spacing} }{ $tick_radius}}, $tick_group_entry;
      }
    }
  }
  
  my ($first_label_idx) = grep( $ticks[$_]{labeldata}, ( 0 .. @ticks - 1 ) );
  my ($last_label_idx)  = grep( $ticks[$_]{labeldata}, reverse( 0 .. @ticks - 1 ) );
  my @tick_idx = sort { $ticks[$a]{pos} <=> $ticks[$b]{pos} } ( 0 .. @ticks - 1 );

  # Determine whether labels of ticks within a spacing group overlap (label_separation)
  # and if so, set the do_not_draw key to suppress their display.
  #
  # This loop also applies tests to the first and last labels of the ideogram
  # to see whether they should be suppressed (skip_first_label, skip_last_label).

  for my $spacing (keys %$tick_groups) {
    for my $radius (keys %{$tick_groups->{$spacing}}) {
      my @tick_with_label = grep($_->{labeldata}, @{$tick_groups->{$spacing}{$radius}});
      next unless @tick_with_label;
      my $label_color;
      if(seek_parameter("skip_first_label",$tick_with_label[0]{tickdata},$CONF{ticks})) {
	$tick_with_label[0]{labeldata}{do_not_draw} = 1;
      }
      if(seek_parameter("skip_last_label",$tick_with_label[-1]{tickdata},$CONF{ticks})) {
	$tick_with_label[-1]{labeldata}{do_not_draw} = 1;
      }

      if (my $sep = $tick_with_label[0]{labeldata}{label_separation}) {
	$sep = unit_strip(unit_validate($sep, "ticks/label_separation", "p"));
	if($sep) {
	  for my $tick_idx (0..@tick_with_label-1) {
	    my $prev_check = $tick_idx ? 
	      $tick_with_label[$tick_idx]{labeldata}{start_a}-$tick_with_label[$tick_idx-1]{labeldata}{end_a}
		: undef;
	    my $next_check = $tick_idx < @tick_with_label-1 ?
	      $tick_with_label[$tick_idx+1]{labeldata}{start_a}-$tick_with_label[$tick_idx]{labeldata}{end_a}
		: undef;
	    if( ( ! defined $prev_check || $prev_check >= $sep)
		&&
		( ! defined $next_check || $next_check >= $sep) ) {
	      # tick label is sufficiently far from neighbours
	    } else {
	      $tick_with_label[$tick_idx]{labeldata}{do_not_draw} = 1;
	      $tick_with_label[$tick_idx]{labeldata}{color}       = "red";
	    }
	  }
	}
      }
    }
  }

  # group url-ticks by r0

  my $tick_idx_map = {};
  for my $tick_idx (@tick_idx) {
    my $tick = $ticks[$tick_idx];
    if($tick->{tickdata}{url}) {
      my $r0 = $tick->{r0}; 
      my $spacing = $tick->{tickdata}{spacing};
      push @{$tick_idx_map->{ $r0 }{$spacing}}, $tick_idx;
    }
  }
  
  # create image map regions
  
  for my $tick_r0 (sort {$a <=> $b} keys %$tick_idx_map) {
    for my $tick_spacing (sort {$a <=> $b} keys %{$tick_idx_map->{$tick_r0}}) {
      my @tick_idx_map = @{$tick_idx_map->{$tick_r0}{$tick_spacing}};
      for my $tick_idx ( @tick_idx_map ) {
	my $tick     = $ticks[$tick_idx];
	next unless $tick->{r0} == $tick_r0;
	my $tickdata = $tick->{tickdata};
	#printinfo($tick->{pos});
	if($tickdata->{url}) {
	  my @pos_pairs;
	  if($tick_idx == $tick_idx_map[0]) {
	    # this is the first tick - check to extend the
	    # map element back to the start of the ideogram if this
	    # tick is not at the start of the ideogram
	    if($tick->{pos} > $ideogram->{set}->min) {
	      my $pos = $tick->{pos};
	      my $prev_pos = $ideogram->{set}->min;
	      push @pos_pairs,[$prev_pos,$pos];
	    }
	  } else {
	    my $prev_tick = $ticks[$tick_idx-1];
	    my $pos = $tick->{pos};
	    my $prev_pos = $prev_tick->{pos};
	    push @pos_pairs,[$prev_pos,$pos];
	  }
	  if($tick_idx == @tick_idx_map[-1]) {
	    if($tick->{pos} < $ideogram->{set}->max) {
	      my $prev_pos = $tick->{pos};
	      my $pos = $ideogram->{set}->max;
	      push @pos_pairs, [$prev_pos,$pos];
	    }
	  }
	  for my $pos_pair (@pos_pairs) {
	    my ($prev_pos,$pos) = @$pos_pair;
	    my $url = seek_parameter("url",$tickdata,$CONF{ticks});
	    $url = format_url(url=>$url,param_path=>[$tickdata,
						     $tick,
						     {start=>$prev_pos,
						      end=>$pos},
						    ]);
	    my ($r0,$r1);
	    if($tickdata->{map_radius_inner}) {
	      $r0 = unit_parse($tickdata->{map_radius_inner},$ideogram);
	    } else {
	      $r0 = $tick->{r0};
	    }
	    if($tickdata->{map_radius_outer}) {
	      $r1 = unit_parse($tickdata->{map_radius_outer},$ideogram);
	    } elsif($tickdata->{map_size}) {
	      my $map_size = unit_strip(unit_validate(seek_parameter("map_size", $tickdata, $CONF{ticks}),
						      "ticks/tick/map_size","p"
						     )
				       );
	      $r1 = $r0 + $map_size;
	    } else {
	      $r1 = $tick->{r1};
	    }
	    #printinfo("tickmap",$r0,$r1);
	    slice(
		  image       => $IM,
		  start       => $prev_pos,
		  end         => $pos,
		  chr         => $chr,
		  radius_from => $r0,
		  radius_to   => $r1,
		  edgecolor   => undef,
		  edgestroke  => undef,
		  fillcolor   => undef,
		  mapoptions => { url=>$url },
		 );
	  }
	}
      }
    }
  }
  
  # draw the ticks
  for my $tick_idx ( @tick_idx ) {
    
    my $tick     = $ticks[$tick_idx];
    my $tickdata = $tick->{tickdata};
    next if $tick->{do_not_draw};
    draw_line(
	      $tick->{coordinates},
	      $DIMS->{tick}{ $tickdata->{dims_key} }{thickness} || 1,
	      $tick->{color}||seek_parameter( "color", $tickdata, $CONF{ticks} ),
	     );
    if ( $tick->{griddata} ) {
      draw_line(
                $tick->{griddata}{coordinates},
                seek_parameter("grid_thickness", $tickdata, $CONF{ticks}, \%CONF ),
                seek_parameter( "grid_color", $tickdata, $CONF{ticks}, \%CONF )
		|| seek_parameter( "color", $tickdata, $CONF{ticks} ),
	       );
    }
    if ( $tick->{labeldata} ) {
      next if $tick->{labeldata}{do_not_draw};
      draw_text(
                image => $IM,
                %{ $tick->{labeldata} },
                mapoptions => {}
	       );
    }
  }
}

sub label_bounds {
  # return bounds for a text box
  my ($font,$size,$text) = @_;
  my @bounds = GD::Image->stringFT($COLORS->{black},$font,$size,0,0,0,$text);
  return @bounds;
}
# -------------------------------------------------------------------
sub process_tick_structure {
  # do some up-front munging of the tick data structures
  my ( $tick, $ideogram ) = @_;

  # handle relatively spaced ticks (e.g. every 0.1), or ticks at
  # specific relative position (e.g. at 0.1)

  if ( seek_parameter( "spacing_type", $tick, $CONF{ticks} ) eq "relative" ) {
    if (!defined seek_parameter( "rspacing|rposition", $tick, $CONF{ticks} ) ) {
      croak "error processing tick - this tick's spacing_type is ",
	"set to relative, but no rspacing or rposition parameter is set";
    }
    if ( seek_parameter( "rspacing", $tick, $CONF{ticks} ) ) {
      if ( unit_validate(seek_parameter( "rspacing", $tick, $CONF{ticks} ),"ticks/tick/rspacing", qw(n)) ) {
	my $mb_rspacing = Math::BigFloat->new(seek_parameter( "rspacing", $tick, $CONF{ticks} ) );

	#
	# this is important - if the divisor for relative tick
	# spacing is the chromosome, then the spacing is
	# relative to the length of the chromosome (default)
	# otherwise, if the divisor is ideogram
	# (rdivisor=ideogram), the spacing is relative to the
	# ideogram
	#
	if (seek_parameter( "rdivisor|label_rdivisor", $tick,$CONF{ticks} ) eq "ideogram" ) {
	  $tick->{spacing} = $mb_rspacing * $ideogram->{set}->cardinality;
	} else {
	  $tick->{spacing} = $mb_rspacing * $ideogram->{chrlength};
	}
	# at this point, spacing does not have to be an integer
	$tick->{spacing} = $tick->{spacing}->bstr;
      }
      #printinfo("spacingdet",$tick->{spacing});
    } elsif ( seek_parameter( "rposition", $tick, $CONF{ticks} ) ) {
      my @rpos =
	map { unit_validate( $_, "ticks/tick/rposition", qw(n) ) }
	  split( /,/, seek_parameter( "rposition", $tick, $CONF{ticks} ) );
      @rpos = map { Math::BigFloat->new($_) } @rpos;

      my $divisor;
      if (
	  seek_parameter(
			 "rdivisor|label_rdivisor", $tick, $CONF{ticks}
			) eq "ideogram"
	 ) {
	$divisor = $ideogram->{set}->cardinality;
      } else {
	$divisor = $ideogram->{chrlength};
      }

      @rpos = map { $_ * $divisor } @rpos;
      $tick->{position} = \@rpos;
    }
  } else {
    if ( ! $tick->{_processed} ) {
      if ( seek_parameter( "spacing", $tick, $CONF{ticks} ) ) {
	$tick->{spacing} = unit_convert(from    => unit_validate(seek_parameter( "spacing", $tick, $CONF{ticks} ),
								 "ticks/tick/spacing", qw(u b)),
					to      => "b",
					factors => { ub => $CONF{chromosomes_units} }
				       );
      } elsif ( seek_parameter( "position", $tick, $CONF{ticks} ) ) {
	my @pos;
	for my $pos (split( /,/,seek_parameter( "position", $tick, $CONF{ticks} ) )) {
	  if($pos eq "start") {
	    $pos = $ideogram->{set}->min . "b";
	  } elsif ($pos eq "end") {
	    $pos = $ideogram->{set}->max . "b";
	  } 
	  push @pos, $pos;
	}
	@pos = map { unit_convert( from    => unit_validate( $_, "ticks/tick/position", qw(u b) ),
				   to      => "b",
				   factors => { ub => $CONF{chromosomes_units} }
				 ) } @pos;
	$tick->{position} = \@pos;
	#$tick->{spacing} = join(",",@pos).$tick->{radius};
      } else {
	croak "error processing tick - this tick's spacing_type is ",
	  "set to absolute, but no spacing or position parameter is set";
      }
    }
  }

  if ( !$tick->{_processed} ) {
    if ( seek_parameter( "grid", $tick, $CONF{ticks} ) ) {
      $tick->{grid_thickness} = unit_strip(
					   unit_validate(
							 (
							  seek_parameter( "grid_thickness", $tick, $CONF{ticks} ),
							  "ticks/*/grid_thickness",
							  qw(p)
							 )
							)
					  );
    }
  }

  my $dims_key = $tick->{spacing} || join($EMPTY_STR, @{ $tick->{position} });
  my @tick_radius;

  if ( $tick->{radius} ) {
    @tick_radius =
      map { unit_parse( $_, $ideogram ) } make_list( $tick->{radius} );
  } else {
    @tick_radius =
      map { unit_parse( $_, $ideogram ) } make_list( $CONF{ticks}{radius} );
  }

  for my $tick_radius (@tick_radius) {
    my $dims_key = join( $COLON, $dims_key, $tick_radius );
    $tick->{dims_key} = $dims_key;

    if ( !exists $DIMS->{tick}{$dims_key} ) {
      $DIMS->{tick}{$dims_key}{size} = unit_convert(
						    from => unit_validate(
									  seek_parameter( "size", $tick, $CONF{ticks} ),
									  "ticks/tick/size", qw(r p)
									 ),
						    to => "p",
						    factors =>
						    {
						     rp => $DIMS->{ideogram}{ $ideogram->{tag} }{thickness} }
						   );

      $DIMS->{tick}{$dims_key}{thickness} = unit_convert(
							 from => unit_validate(
									       seek_parameter( "thickness", $tick, $CONF{ticks} ),
									       "ticks/tick/tickness", qw(r p)
									      ),
							 to      => "p",
							 factors => { rp => $DIMS->{tick}{ $tick->{spacing} }{size} }
							);

      if (
	  defined seek_parameter(
				 "min_label_distance_to_edge", $tick, $CONF{ticks}
				)
	 ) {
	$DIMS->{tick}{$dims_key}{min_label_distance_to_edge} 
	  = unit_validate(
			  seek_parameter(
					 "min_label_distance_to_edge", $tick, $CONF{ticks}
					),
			  "ticks/tick/min_label_distance_to_edge",
			  "p"
			 );
      }
    }
  }
  $tick->{_radius} = \@tick_radius;
  $tick->{_processed}++;
}

# -------------------------------------------------------------------
sub ideogram_spacing_helper {
  #
  # given two adjacent ideograms, determine the spacing between them
  #
  # return spacing in bases
  #
  my $value = shift;
  unit_validate( $value, "ideogram/spacing/pairwise", qw(u r) );
  my $spacing;

  if ( unit_fetch( $value, "ideogram/spacing/pairwise" ) eq "u" ) {
    $spacing = unit_strip($value) * $CONF{chromosomes_units};
  } elsif ( unit_fetch( $value, "ideogram/spacing/pairwise" ) eq "r" ) {
    $spacing = unit_strip($value) * $DIMS->{ideogram}{spacing}{default};
  }
  return $spacing;
}

# -------------------------------------------------------------------
sub ideogram_spacing {
  my ( $id1,  $id2 )  = @_;
  my ( $chr1, $chr2 ) = ( $id1->{chr}, $id2->{chr} );
  my ( $tag1, $tag2 ) = ( $id1->{tag}, $id2->{tag} );

  $DIMS->{ideogram}{spacing}{default} = unit_convert(
						     from    => $CONF{ideogram}{spacing}{default},
						     to      => "b",
						     factors => {
								 ub => $CONF{chromosomes_units},
								 rb => $GSIZE_NOSCALE
								}
						    );

  my $spacing = $DIMS->{ideogram}{spacing}{default};
  my @keys = ( $chr1, $chr2, $tag1, $tag2 );
  my $spacing_found;

 KI1:
  for my $ki ( 0 .. $#keys - 1 ) {
    for my $kj ( 0 .. $#keys - 1 ) {
      next if $kj == $ki;
      my $key = join( $SEMICOLON, @keys[ $ki, $kj ] );
      if ( exists $CONF{ideogram}{spacing}{pairwise}{$key} ) {
	$spacing = ideogram_spacing_helper(
					   $CONF{ideogram}{spacing}{pairwise}{$key}{spacing} );
	$spacing_found = 1;
	last KI1;
      }
    }
  }

 KI2:
  for my $ki ( 0 .. $#keys - 1 ) {
    if ( !$spacing_found ) {
      my $key = $keys[$ki];
      if ( exists $CONF{ideogram}{spacing}{pairwise}{$key} ) {
	$spacing = ideogram_spacing_helper(
					   $CONF{ideogram}{spacing}{pairwise}{$key}{spacing} );
	$spacing_found = 1;
	last KI2;
      }
    }
  }

  if ( !$spacing_found ) {
    if ( $chr1 eq $chr2 ) {
      my $value = $CONF{ideogram}{spacing}{break}
	|| $CONF{ideogram}{spacing}{default};
      $spacing = ideogram_spacing_helper($value);
    }
  }

  if ( $id1->{break}{end} && $chr1 ne $chr2 ) {
    my $value = $CONF{ideogram}{spacing}{break} || $CONF{ideogram}{spacing}{default};
    $spacing += ideogram_spacing_helper($value);
    $id1->{break}{end} = $value;
    $DIMS->{ideogram}{break}{ $id1->{chr} }{end} = $value;
  }

  if ( $id2->{break}{start} && $chr1 ne $chr2 ) {
    my $value = $CONF{ideogram}{spacing}{break} || $CONF{ideogram}{spacing}{default};
    $spacing += ideogram_spacing_helper($value);
    $id2->{break}{start} = $value;
    $DIMS->{ideogram}{break}{ $id2->{chr} }{start} = $value;
  }

  $DIMS->{ideogram}{spacing}{ sprintf( "%d;%d", $id1->{idx}, $id2->{idx} ) } =
    $spacing;
  $DIMS->{ideogram}{spacing}{ sprintf( "%d;%d", $id2->{idx}, $id1->{idx} ) } =
    $spacing;

  return $spacing;
}

################################################################
# parse ideogram order from parameter or file
sub read_chromosomes_order {
  my @chrorder;
  # construct a list of ordered chromosomes, from one of
  # - 'chromosomes_order' parameter
  # - 'chromosomes_order_file' input file
  # - native order from karyotype
  if ( $CONF{chromosomes_order} ) {
    @chrorder = split( /\s*[;,]\s*/, $CONF{chromosomes_order} );
  } elsif ( $CONF{chromosomes_order_file} ) {
    $CONF{chromosomes_order_file} = locate_file( $CONF{chromosomes_order_file} );
    open CHRORDER, $CONF{chromosomes_order_file} 
      or confess "Cannot open $CONF{chromosomes_order_file}: $!\n";
    while (<CHRORDER>) {
      chomp;
      my ($tag) = split;
      push( @chrorder, $tag );
    }
    close(CHRORDER);
  } else {
    @chrorder = ($CARAT, 
		 sort { $KARYOTYPE->{$a}{chr}{display_order} <=> $KARYOTYPE->{$b}{chr}{display_order} } keys %$KARYOTYPE
		);
  }

  my %seen_tag;
  my @tags = map { $_->{tag} =~ /__/ ? $_->{chr} : $_->{tag} } @IDEOGRAMS;
  my $n;
  for my $tag (@chrorder) {
    my $tag_found = grep( $_ eq $tag, @tags );
    if ($tag_found) {
      if ( $seen_tag{$tag}++ ) {
	confess "fatal error - incorrectly formatted chromosomes_order field (or content of chromosomes_order_file) - tag $tag appears multiple times.";
      }
    } elsif ( $tag ne $PIPE && $tag ne $DOLLAR && $tag ne $CARAT && $tag ne $DASH
	       && ! grep($_->{tag} eq $tag, @IDEOGRAMS)
	      && ! grep($_ eq $tag, keys %$KARYOTYPE) ) {
      confess "fatal error - incorrectly formatted chromosomes_order field (or content of chromosomes_order_file) - tag $tag appears in the chromosome order, but it is not associated with any chromosome.";
    }
    $n++ if $tag_found || $tag eq $DASH;
  }
  if ( $n > @IDEOGRAMS ) {
    printwarning(
		 "you have more tags ($n) in the chromosomes_order field than ideograms (",
		 int(@IDEOGRAMS),
		 ") - circos may not be able to correctly order the display"
		);
  }
  return @chrorder;
}

################################################################
# chromosomes and regions can have a scale multiplier to adjust
# the size of the ideogram in the image
#
# scale is keyed by the chromosome/region tag and applied
# in the order of appearance in the scale string
#
sub register_chromosomes_scale {
  my @chrs = split( /[;,]/, $CONF{chromosomes_scale} );
  for my $pair (@chrs) {
    my ( $tag, $scale ) = split( /:/, $pair );
    for my $ideogram (@IDEOGRAMS) {
      $ideogram->{scale} = $scale if $ideogram->{tag} eq $tag;
    }
  }
}

################################################################
# chromosomes and regions may be reversed
#
sub register_chromosomes_direction {
  my @chrs = split( /[;,]/, $CONF{chromosomes_reverse} );
  for my $pair (@chrs) {
    my ( $tag, $scale ) = split( /:/, $pair );
    for my $ideogram (@IDEOGRAMS) {
      $ideogram->{reverse} = 1 if $ideogram->{tag} eq $tag;
    }
  }
}

# -------------------------------------------------------------------
sub register_chromosomes_radius {
  my @chrs = split( /[;,]/, $CONF{chromosomes_radius} );

  #
  # Each ideogram can be at a different radius, but for now register the
  # default position for ideograms.
  #
  $DIMS->{ideogram}{default}{radius} = unit_convert(
						    from =>
						    unit_validate( $CONF{ideogram}{radius}, "ideogram/radius", qw(r p) ),
						    to      => "p",
						    factors => { rp => $DIMS->{image}{radius} }
						   );

  $DIMS->{ideogram}{default}{thickness} = unit_convert(
						       from => unit_validate(
									     $CONF{ideogram}{thickness},
									     "ideogram/thickness", qw(r p)
									    ),
						       to      => "p",
						       factors => { rp => $DIMS->{image}{radius} }
						      );

  $DIMS->{ideogram}{default}{radius_inner} =
    $DIMS->{ideogram}{default}{radius} -
      $DIMS->{ideogram}{default}{thickness};

  $DIMS->{ideogram}{default}{radius_outer} =
    $DIMS->{ideogram}{default}{radius};

  $DIMS->{ideogram}{default}{label}{radius} =
    unit_parse( $CONF{ideogram}{label_radius} );

  #
  # legacy
  #
  $DIMS->{ideogram}{thickness} = $DIMS->{ideogram}{default}{thickness};
  #
  # end legacy
  #

 PAIR:
  for my $pair (@chrs) {
    my ( $tag, $radius ) = split( /:/, $pair );

    $DIMS->{ideogram}{$tag}{radius} = unit_convert(
						   from => unit_validate( $radius, "ideogram/radius", qw(r p) ),
						   to   => "p",
						   factors => { rp => $DIMS->{ideogram}{default}{radius} }
						  );

    for my $ideogram (@IDEOGRAMS) {
      if ( $ideogram->{tag} eq $tag || $ideogram->{chr} eq $tag ) {
	$ideogram->{radius}       = $DIMS->{ideogram}{$tag}{radius};
	$ideogram->{radius_outer} = $DIMS->{ideogram}{$tag}{radius};
	$ideogram->{radius_inner} =
	  $DIMS->{ideogram}{$tag}{radius} -
	    $DIMS->{ideogram}{default}{thickness};
      }
    }
  }

  #
  # By default, each ideogram's radial position is the default one,
  # set within the <ideogram> block by radius and thickness. Apply
  # this default setting if a custom radius has not been defined.
  #
  for my $ideogram (@IDEOGRAMS) {
    printinfo( "registering tag", $ideogram->{tag} );

    $ideogram->{radius}       ||= $DIMS->{ideogram}{default}{radius};
    $ideogram->{radius_outer} ||= $DIMS->{ideogram}{default}{radius_outer};
    $ideogram->{radius_inner} ||= $DIMS->{ideogram}{default}{radius_inner};
    $ideogram->{thickness}    ||= $DIMS->{ideogram}{default}{thickness};

    $DIMS->{ideogram}{ $ideogram->{tag} }{radius} ||= $ideogram->{radius};
    $DIMS->{ideogram}{ $ideogram->{tag} }{radius_inner} ||=
      $ideogram->{radius_inner};
    $DIMS->{ideogram}{ $ideogram->{tag} }{radius_outer} ||=
      $ideogram->{radius_outer};
    $DIMS->{ideogram}{ $ideogram->{tag} }{thickness} ||=
      $ideogram->{thickness};
    $DIMS->{ideogram}{ $ideogram->{tag} }{label}{radius} ||=
      unit_parse( $CONF{ideogram}{label_radius}, $ideogram );
  }
}

# -------------------------------------------------------------------
sub get_ideogram_radius {
  my $ideogram = shift;

  if ( defined $DIMS->{ideogram}{ $ideogram->{tag} } ) {
    return $DIMS->{ideogram}{ $ideogram->{tag} }{radius};
  } else {
    return $DIMS->{ideogram}{default}{radius};
  }
}

################################################################
#
sub create_ideogram_set {
  my @chrs = @_;
  my $tag_count;
  for my $chr (@chrs) {
    next unless $chr->{accept};
    my $chrname = $chr->{chr};
    my $region_candidate =  $chr->{set}->intersect($KARYOTYPE->{$chrname}{chr}{display_region}{accept} );
    next unless $region_candidate->cardinality;
    $KARYOTYPE->{ $chrname }{chr}{ideogram} = 1;
    for my $set ( $region_candidate->sets ) {
      if ( $chr->{tag} eq "default" ) {
	confess "fatal error - you have an ideogram with the tag",
	  "[default] which is not allowed as this is a ",
	    "reserved keyword";
      }
      ################################################################
      # v0.52
      # chromosomes that don't have an explicit tag, receive an automatically
      # generated tag if autotag=yes. 
      my $autotag = sprintf("%s__%d",$chr->{chr},$tag_count->{ $chr->{chr} }++);
      my $idtag;
      if($chr->{tag} eq $chr->{chr} && $CONF{autotag}) {
	$idtag = $autotag;
      } else {
	$idtag = $chr->{tag};
      }
      my $ideogram = {
		      chr       => $chr->{chr},
		      chrlength => $KARYOTYPE->{ $chrname }{chr}{size},
		      label     => $KARYOTYPE->{ $chrname }{chr}{label},
		      param     => $KARYOTYPE->{ $chrname }{chr}{options},
		      scale     => 1,
		      reverse   => 0,
		      tag       => $idtag,
		      idx       => int(@IDEOGRAMS),
		      set       => $set,
		     };
      push @IDEOGRAMS, $ideogram;
    }
  }

  ################################################################
  # v0.52 This section is deprecated (I think). 
  # RUN TESTS TO ENSURE THAT THIS LOOP IS NOT REQUIRED.
  #
  # Scan for chromosome entries that have accept regions but have not been
  # added to @IDEOGRAMS. 
  for my $chrname ( sort keys %$KARYOTYPE ) {
    my $chr = $KARYOTYPE->{$chrname}{chr};
    next if defined $chr->{ideogram};
    next unless $chr->{display_region}{accept}->cardinality;
    $chr->{ideogram} = 1;
    my $autotag = sprintf("%s__%d",$chr->{chr},$tag_count->{ $chrname }++);
    my $idtag;
    if($chr->{tag} eq $chr->{chr} && $CONF{autotag}) {
      $idtag = $autotag;
    } else {
      $idtag = $chr->{tag};
    }
    for my $set ($chr->{display_region}{accept}->sets) {
      if ( $chr eq "default" ) {
	confess "fatal error - you have an ideogram with the name ",
	  "[default] which is not allowed as this is a ",
	    "reserved keyword";
      }
      push @IDEOGRAMS, {
			chr       => $chrname,
			label     => $chr->{label},
			chrlength => $chr->{size},
			label     => $chr->{label},
			param     => $chr->{options},
			scale     => 1,
			reverse   => 0,
			tag   => $idtag,
			idx   => int(@IDEOGRAMS),
			set   => $set,
		       };
    }
  }
  return sort { $a->{idx} <=> $b->{idx} } @IDEOGRAMS;
}

################################################################
# Ensure that each chromosome in the karyotype has a display_region
# field.
#
# Any reject/accept regions defined in parse_chromosomes() are checked
# against the size of the chromosome and intersected with the extent
# of the chromosome.
#
# This function modifies the {CHR}{chr}{display_region} hash by 
# adjusting 'accept' and 'reject' keys.
#
sub refine_display_regions {
  for my $chr ( sort {$KARYOTYPE->{$a}{chr}{display_order} <=> $KARYOTYPE->{$b}{chr}{display_order}} keys %$KARYOTYPE ) {
    $KARYOTYPE->{$chr}{chr}{display_region} ||= {};

    my $region = $KARYOTYPE->{$chr}{chr}{display_region};

    if ( $region->{reject} && $region->{accept} ) {
      $region->{reject} = $region->{reject}->intersect( $KARYOTYPE->{$chr}{chr}{set} );
      $region->{accept} = $region->{accept}->intersect( $KARYOTYPE->{$chr}{chr}{set} )->diff( $region->{reject} );
    } elsif ( $region->{reject} ) {
      $region->{reject} = $region->{reject}->intersect( $KARYOTYPE->{$chr}{chr}{set} );
      $region->{accept} = $KARYOTYPE->{$chr}{chr}{set}->diff( $region->{reject} );
    } elsif ( $region->{accept} ) {
      $region->{accept} = $region->{accept}->intersect( $KARYOTYPE->{$chr}{chr}{set} );
      $region->{reject} = Set::IntSpan->new();
    } else {
      if ( $CONF{chromosomes_display_default} ) {
	$region->{accept} = $KARYOTYPE->{$chr}{chr}{set};
	$region->{reject} = Set::IntSpan->new();
      } else {
	$region->{reject} = Set::IntSpan->new();
	$region->{accept} = Set::IntSpan->new();
      }
    }

    $KARYOTYPE->{$chr}{chr}{display} = $region->{accept}->cardinality ? 1 : 0;

    printdebug(
	       "chromosome ranges",      $chr,
	       "display",                $KARYOTYPE->{$chr}{chr}{display},
	       "region_display",         $region->{accept}->run_list,
	       "region_explicit_reject", $region->{reject}->run_list
	      );
  }
}

sub merge_ideogram_filters {
  # Merges multiple ideogram filters into a single filter by taking
  # the union of all sets for a given type (show, hide) and
  # ideogram. This function also creates a new type (combined) which 
  # is show->diff(hide)
  my @filters = @_;
  my $merged_filter;
  my %chrs;
  for my $filter (@filters) {
    for my $chr (keys %$filter) {
      for my $type (keys %{$filter->{$chr}}) {
	if($merged_filter->{$chr}{$type}) {
	  $merged_filter->{$chr}{$type}->U( $filter->{$chr}{$type} );
	} else {
	  $merged_filter->{$chr}{$type} = $filter->{$chr}{$type};
	}
      }
    }
  }
  for my $chr (keys %$merged_filter) {
    if(exists $merged_filter->{$chr}{show}) {
      if(exists $merged_filter->{$chr}{hide}) {
	$merged_filter->{$chr}{combined} = $merged_filter->{$chr}{show}->diff($merged_filter->{$chr}{hide});
      } else {
	$merged_filter->{$chr}{combined} = $merged_filter->{$chr}{show};
      }
    } else {
      if(exists $merged_filter->{$chr}{hide}) {
	$merged_filter->{$chr}{combined} = Set::IntSpan->new("(-)")->diff($merged_filter->{$chr}{hide});
      } else {
	$merged_filter->{$chr}{combined} = Set::IntSpan->new("(-)");
      }
    }
  }
  return $merged_filter;
}

sub parse_ideogram_filter {
  # Parse a tick's ideogram filter. The format of this filter string is the same
  # as for the chromosomes parameter. The filter data structure defines
  # an ideogram (and its range) as either shown or hidden
  #
  # $filter->{CHR}{hide} = RANGE
  # $filter->{CHR}{show}     = RANGE
  #
  # TODO There is some duplication between this function and parse_chromosomes(). 
  # Common functionality should be centralized.

  my $filter_string = shift;
  my $filter = {};
  return $filter if ! defined $filter_string;

  for my $chr (split(/;/,$filter_string)) {
    my ($suppress,$tag,$runlist) = $chr =~ /(-)?([^:]+):?(.*)/;
    if ( $CONF{chromosomes_units} ) {
      $runlist =~ s/([\.\d]+)/$1*$CONF{chromosomes_units}/eg;
    }
    my $is_suppressed = $suppress ? 1 : 0;
    my $set = Set::IntSpan->new( $runlist || "(-)" );
    if($is_suppressed) {
      $filter->{$tag}{hide} = $set;
    } else {
      $filter->{$tag}{show} = $set;
    }
  }
  return $filter;
}

################################################################
#
# Determine which chromosomes are going to be displayed. Several parameters
# are used together to determine the list and order of displayed chromosomes.
#
# - chromosomes
# - chromosomes_breaks
# - chromosomes_display_default
# - chromosomes_order_by_karyotype
#
# If chromosomes_display_default is set to 'yes', then any chromosomes that
# appear in the karyotype file that DO NOT APPEAR in the 'chromosomes' parameter
# are appended to the 'chromosomes' parameter. The order in which they
# are appended depends on the value of 'chromosomes_order_by_karyotype'.
# 
# If you want to display only those chromosomes that are mentioned in the 
# 'chromosomes' parameter, then set chromosomes_display_default=no.
#
# Both 'chromosomes' and 'chromosomes_breaks' define a list of chromosome regions
# to show, delimited by ;
#
# name{[tag]}{:runlist}
#
# e.g.   hs1
#        hs1[a]
#        hs1:0-100
#        hs1[a]:0-100
#        hs1[a]:0-100,150-200
#        hs1;hs2[a];hs3:0-100
#
# The functional role of 'chromosomes' and 'chromosomes_breaks' is the same. The latter
# gives an opportunity to syntactically separate definitions of regions which are not shown.
# 
sub parse_chromosomes {

  my @chrs;
  if ( $CONF{chromosomes_display_default} ) {
    #
    # The default order for chromosomes is string-then-number if
    # chromosomes contain a number, and if not then asciibetic
    # I used to have this based on the order in the KARYOTYPE (use
    # {CHR}{chr}{display_order} field) but decided to change it.
    #
    my @chrs_tmp;
    if ( $CONF{chromosomes_order_by_karyotype} ) {
      @chrs_tmp = sort {
	$KARYOTYPE->{$a}{chr}{display_order} <=> $KARYOTYPE->{$b}{chr}{display_order}
	} grep( $KARYOTYPE->{$_}{chr}, keys %$KARYOTYPE );
    } else {
      @chrs_tmp = sort {
	$a =~ /\d/ && $b =~ /\d/
	  ? ( ( $a =~ /^(\D+)/ )[0] cmp( $b =~ /^(\D+)/ )[0] )
	    || ( ( $a =~ /(\d+)/ )[0] <=> ( $b =~ /(\d+)/ )[0] )
	      : $a cmp $b
            } grep( $KARYOTYPE->{$_}{chr}, keys %$KARYOTYPE );
    }

    # Remove from the default list any chromosomes mentioned in the chromosomes field.
    if ( $CONF{chromosomes} ) {
      @chrs_tmp = grep { $CONF{chromosomes} !~ /\b$_\b/ } @chrs_tmp;
    }

    # Reconstruct the 'chromosomes' parameter from the 'chromosomes' parameter and
    # the default list.
    if (@chrs_tmp) {
      if($CONF{chromosomes} ) {
	$CONF{chromosomes} = join( $SEMICOLON, $CONF{chromosomes}, join( $SEMICOLON, @chrs_tmp ) );
      } else {
	$CONF{chromosomes} = join( $SEMICOLON, @chrs_tmp );
      }
    }
  }
  
  for my $pair ([$CONF{chromosomes},1],
		[$CONF{chromosomes_breaks},0]) {
    my ($string,$accept_default) = @$pair;
    for my $chrstring (split(/[; ]+/,$string)) {
      my ($chr,$runlist) = split($COLON,$chrstring);
      $chr       = $EMPTY_STR if !defined $chr;
      $runlist   = $EMPTY_STR if !defined $runlist;
      # $accept identifies whether the regions indicate inclusions or exclusions
      # $accept=1 this region is to be included
      # $accept=0 this region is to be included (region prefixed by -)
      my $accept = $accept_default;
      $accept = 0 if $chr =~ s/^-//;
      # each chromosome region may have a tag, delimited by [ and ] (e.g. chr[tag]:runlist)
      # hs1[a];hs2[b]:0-100;...
      my $tag;
      ( $chr, $tag ) = $chr =~ /([^\[\]]+)\[?([^\]]*)\]?$/;
      if ( ! defined $KARYOTYPE->{$chr}{chr} ) {
	confess "fatal error - entry in 'chromosomes' parameter [$chrstring] mentions chromosome [$chr] which is not defined the karyotype file.";
      };
      
      # all numbers in runlist are automatically multiplied by
      # chromosomes_units value - this saves you from having to type
      # a lot of zeroes in the runlists
      
      if ( $CONF{chromosomes_units} ) {
	$runlist =~ s/([\.\d]+)/$1*$CONF{chromosomes_units}/eg;
      }
      
      printdebug( "parsed chromosome range", $chr, $runlist || $DASH );
      
      my $set = $runlist ? Set::IntSpan->new($runlist) : $KARYOTYPE->{$chr}{chr}{set};
      
      ################################################################
      # uncertain - what was I trying to do here?
      $set->remove($set->max) if $runlist;
      if ( ! $accept ) {
	$set->remove( $set->min ) if $set->min;
	$set->remove( $set->max );
      }
      ################################################################
      
      if ($accept) {
	push @chrs,
	  {
	   chr    => $chr,
	   tag    => $tag || $chr,
	   idx    => int(@chrs),
	   accept => $accept,
	   set    => $set
	  };
      }
      
      if ($accept) {
	$KARYOTYPE->{$chr}{chr}{display_region}{accept} ||= Set::IntSpan->new();
	$KARYOTYPE->{$chr}{chr}{display_region}{accept} = $KARYOTYPE->{$chr}{chr}{display_region}{accept}->union($set);
      } else {
	$KARYOTYPE->{$chr}{chr}{display_region}{reject} ||= Set::IntSpan->new();
	$KARYOTYPE->{$chr}{chr}{display_region}{reject} = $KARYOTYPE->{$chr}{chr}{display_region}{reject}->union($set);
      }
    }
  }
  
  if ( ! grep( $_->{accept}, @chrs ) ) {
    confess "no chromosomes to draw - either define some in 'chromosomes' parameter or set chromosomes_display_default=yes";
  }

  return @chrs;
}

# -------------------------------------------------------------------
sub report_chromosomes {
  for my $chr (
	       sort {
		 $KARYOTYPE->{$a}{chr}{display_order} <=> $KARYOTYPE->{$b}{chr}{display_order}
	       } keys %$KARYOTYPE
	      ) {
    next unless $KARYOTYPE->{$chr}{chr}{display};

    printinfo(
	      $chr,
	      $KARYOTYPE->{$chr}{chr}{display_order},
	      $KARYOTYPE->{$chr}{chr}{scale},
	      $KARYOTYPE->{$chr}{chr}{display_region}
	      ? $KARYOTYPE->{$chr}{chr}{display_region}->run_list
	      : $DASH,
	      $KARYOTYPE->{$chr}{chr}{length_cumul}
	     );
  }
}

# -------------------------------------------------------------------
sub draw_text {
  validate(
	   @_,
	   {
            image         => { isa  => 'GD::Image' },
            color         => 1,
            font          => 1,
            size          => 1,
            angle         => 1,
            pangle        => 0,
            radius        => 0,
            forcerotation => 0,
            text          => 1,
            xy            => { type => ARRAYREF },
            svgxy         => { optional => 1, type => ARRAYREF },
            svgangle      => { optional => 1 },
            chr           => 1,
            start         => 1,
            end           => 1,
            start_a       => 0,
            end_a         => 0,
	    label_separation=>0,
            mapoptions    => { type => HASHREF, optional => 1 },
	   }
	  );

  my %params = @_;

  my @bounds = GD::Image->stringFT(
				   $COLORS->{ $params{color} },
				   @params{qw(font size angle)},
				   @{ $params{xy} },
				   $params{text}
				  );

  my ( $w, $h ) = text_label_size(@bounds);

  if ( $params{svgxy} && $params{svgangle} ) {
    my $tanchor = "start";

    printdebug( "svglabel", $params{text}, $params{pangle} );

    if ( $params{pangle} > 90 && $params{pangle} < 270 ) {
      $tanchor = "end";
    }

    printdebug( "svgangle", $params{svgangle}, $tanchor );

    my $svg = sprintf(
		      qq{<text x="%.1f" y="%.1f" style="fill: rgb(%d,%d,%d); font-size: %.1fpx; text-anchor: %s" transform="rotate(%.1f,%.1f,%.1f)">%s</text>},
		      @{ $params{svgxy} },
		      rgb_color( $params{color} ),
		      $CONF{svg_font_scale} * $params{size},
		      $tanchor,
		      $params{svgangle} + $params{forcerotation},
		      @{ $params{svgxy} },
		      $params{text}
		     );
    printsvg($svg);
  }

  @bounds = $IM->stringFT(
			  $COLORS->{ $params{color} },
			  @params{qw(font size)},
			  $params{angle} + $params{forcerotation} * $DEG2RAD,
			  @{ $params{xy} },
			  $params{text}
			 ) if $PNG_MAKE;

  # contribute to image map
  if(defined $params{mapoptions}{url}) {
    my $xshift = $CONF{image}{image_map_xshift}||0;
    my $yshift = $CONF{image}{image_map_xshift}||0;
    my $xmult  = $CONF{image}{image_map_xfactor}||1;
    my $ymult  = $CONF{image}{image_map_yfactor}||1;
    my @coords = map { ( $bounds[2*$_]*$xmult + $xshift , $bounds[2*$_+1]*$ymult + $yshift ) } (0..3);
    report_image_map(shape=>"poly",
		     coords=>\@coords,
		     href=>$params{mapoptions}{url});
  }
}

# -------------------------------------------------------------------
sub read_plotdata {
  #
  # 2D data plots
  #
  # chr pos y-value option=value,option=value,...
  #
  my $file = shift;
  my %data;
  open( D, $file ) || confess "Cannot open plot file $file";
  while (<D>) {
    chomp;
    next if /^\s*\#/;
    my ( $chr, $pos, $value, $options ) = split;
    my @options = split( /,/, $options );
    push(
	 @{ $data{$chr} },
	 {
	  chr   => lc $chr,
	  pos   => $pos,
	  value => $value,
	  map { split( /=/, $_ ) } @options
	 }
        );
  }
  close(D);
  return \%data;
}

# -------------------------------------------------------------------
sub make_list {
  #
  # if passed an array ref, dereferences it and returns a list
  # if passed a list, returns the list
  # if passed undef/false returns an empty list
  #
  my $obj = shift or return ();

  if ( ref $obj eq 'ARRAY' ) {
    return @$obj;
  } else {
    return ( $obj );
  }
}

# -------------------------------------------------------------------
sub relradius {
  my $radius = shift;

  if ( $radius < 2 ) {
    return $radius * $DIMS->{image}{radius};
  } else {
    return $radius;
  }
}

# -------------------------------------------------------------------
sub allocate_colors {
  return undef if !$PNG_MAKE;

  my $image            = shift;
  my $add_transparent  = shift || 0;
  my $maxcolors        = $CONF{image}{"24bit"} ? 16777216 : 256;
  my $allocated_colors = 0;
  my $colors;

  for my $color ( keys %{ $CONF{colors} } ) {
    next if $color eq "transparent";
    my $colorvalue = $CONF{colors}{$color};

    $colorvalue = $CONF{colors}{$colorvalue} if exists $CONF{colors}{$colorvalue};

    if ( $colorvalue !~ /,/ ) {
      next;
    }

    my @rgb = split( /[, ]+/, $colorvalue );

    if ( @rgb == 3 ) {
      eval {
	my $clr = $image->colorExact(@rgb);
	if ( $CONF{image}{"24bit"} || $clr == -1 ) {
	  if ( $add_transparent + $allocated_colors == $maxcolors ) {
	    if ( !$CONF{image}{"24bit"} ) {
	      die "error - cannot allocate more than ",
		"$maxcolors colors - use 24-bit mode ",
		  "(set 24bit=yes in <image> block) if you ",
		    "need more than $maxcolors colors";
	    } else {
	      die "error - cannot allocate more than ",
		"$maxcolors colors - Circos does not support ",
		  "PNG files with greater color depth than 24-bits";
	    }
	  }

	  $colors->{$color} = $image->colorAllocate(@rgb);
	  $allocated_colors++;
	} else {
	  $colors->{$color} = $clr;
	}
      };

      if ($@) {
	croak "error in allocate_colors for color [$colorvalue] [$@]";
      }
    } elsif ( @rgb == 4 ) {
      $rgb[3] *= 127 if $rgb[3] < 1;
      if ( !$CONF{image}{"24bit"} ) {
	croak "error - you've asked for a color with alpha channel ",
	  "but do not have 24-bit mode set - use 24-bit mode (set ",
	    "24bit=yes in <image> block";
      }

      eval {
	$colors->{$color} = $image->colorAllocateAlpha(@rgb);
	$allocated_colors++;
      };

      if ($@) {
	croak "error in allocate_colors for color ",
	  "[$colorvalue] with alpha channel [$@]";
      }
    }
  }

  #
  # Automatically allocate colors with alpha values, if asked for.
  # The number of steps is determined by auto_alpha_steps in the
  # <image> block
  # Colors with alpha values have names COLOR_aN for N=1..num_steps
  # The alpha value (out of max 127) for step i is 127*i/(num_steps+1)
  #
  # For example, if the number of steps is 5, then for the color
  # chr19=153,0,204, the follow additional 5 colors will be
  # allocated (see full list with -debug)
  #
  # auto_alpha_color chr19_a1 153 0 204 21 17%
  # auto_alpha_color chr19_a2 153 0 204 42 33%
  # auto_alpha_color chr19_a3 153 0 204 64 50%
  # auto_alpha_color chr19_a4 153 0 204 85 67%
  # auto_alpha_color chr19_a5 153 0 204 106 83%
  #
  if ( $CONF{image}{auto_alpha_colors} ) {
    if ( !$CONF{image}{'24bit'} ) {
      croak "error - you've asked for a auto_alpha_colors but do not ",
	"have 24-bit mode set - use 24-bit mode (set 24bit=yes in ",
	  "<image> block";
    }

    my @c = keys %$colors;
    for my $colorname (@c) {
      my @rgb = $image->rgb( $colors->{$colorname} );
      for my $i ( 1 .. $CONF{image}{auto_alpha_steps} ) {
	my $alpha =
	  round( 127 * $i / ( $CONF{image}{auto_alpha_steps} + 1 ) );
	my $aname = $colorname . "_a$i";
	$colors->{$aname} = $image->colorAllocateAlpha( @rgb, $alpha );
      }
    }
  }

  if ($add_transparent) {
    my ( $r, $g, $b );
    if ( $CONF{transparentrgb} ) {
      ( $r, $g, $b ) = split( $COMMA, $CONF{transparentrgb} );
      if (   $CONF{image}{"24bit"}
	     || $image->colorExact( $r, $g, $b ) == -1 
	 ) {
	$colors->{transparent} = $image->colorAllocate( $r, $g, $b );
      } else {
	croak "error - the requested transparent RGB value ",
	  "$r,$g,$b is already allocated to another color";
      }
    } else {
      do {
	( $r, $g, $b ) = map { int( rand(256) ) } ( 0 .. 2 );
	if (   $CONF{image}{"24bit"}
	       || $image->colorExact( $r, $g, $b ) == -1 ) {
	  $colors->{transparent} =
	    $image->colorAllocate( $r, $g, $b );
	}
      } while ( !$colors->{transparent} );
    }
  }

  for my $color ( keys %{ $CONF{colors} } ) {
    my $colorvalue = $CONF{colors}{$color};
    if ( $colorvalue !~ /,/ && exists $colors->{$colorvalue} ) {
      #printinfo( $color, $colorvalue );
      $colors->{$color} = $colors->{$colorvalue};
      $CONF{colors}{$color} = $CONF{colors}{$colorvalue};
    }
  }

  return $colors;
}

# -------------------------------------------------------------------
sub rgb_color_opacity {
  # Returns the opacity of a color, based on its name. Colors with a
  # trailing _aNNN have a transparency level in the range
  # 0..auto_alpha_steps. 
  my $color = shift;
  return 1 if ! defined $color;
  if ( $color =~ /(.+)_a(\d+)/ ) {
    unless ( $CONF{image}{auto_alpha_colors}
	     && $CONF{image}{auto_alpha_steps}
	   ) {
      die "you are trying to process a transparent color ($color) ",
	"but do not have auto_alpha_colors or auto_alpha_steps defined";
    }
    my $color_root = $1;
    my $opacity    = 1 - $2 / $CONF{image}{auto_alpha_steps};
  } else {
    return 1;
  }
}

# -------------------------------------------------------------------
sub rgb_color_transparency {
  my $color = shift;
  return 1 - rgb_color_opacity($color);
}

# -------------------------------------------------------------------
sub rgb_color {
  my $color = shift;
  if ( $color =~ /(.+)_a(\d+)/ ) {
    my $color_root = $1;
    return rgb_color($color_root);
  } else {
    # bug fix v0.41 - PNG colors are not allocated if SVG is used;
    # thus look directly in color config file
    return undef unless $CONF{colors}{$color};
    my @rgb = split( $COMMA, $CONF{colors}{$color} );
    return @rgb;
  }
}

# -------------------------------------------------------------------
sub arc_points {
  validate(
	   @_,
	   {
            start  => 1,
            end    => 1,
            chr    => 1,
            radius => 1,
	   }
	  );

  my %params = @_;
  my ( $start_a, $end_a ) = (
			     getanglepos( $params{start}, $params{chr} ),
			     getanglepos( $params{end},   $params{chr} )
			    );
  my $step_a = $start_a < $end_a ? $CONF{anglestep} : -$CONF{anglestep};

  my ( $x_prev, $y_prev, @points, @angles );
  if ( $start_a < $end_a ) {
    for ( my $angle = $start_a ; $angle <= $end_a ; $angle += $step_a ) {
      push @angles, $angle;
    }
  } else {
    for ( my $angle = $start_a ; $angle >= $end_a ; $angle += $step_a ) {
      push @angles, $angle;
    }
  }

  for my $angle (@angles) {
    my ( $x, $y ) = getxypos( $angle, $params{radius} );

    my $d = sqrt( ( $x - $x_prev )**2 + ( $y - $y_prev )**2 );

    next if defined $x_prev && $d < $CONF{minslicestep};

    ( $x_prev, $y_prev ) = ( $x, $y );

    push @points, [ $x, $y ];

    last if ( $start_a == $end_a );
  }

  push @points, [ getxypos( $end_a, $params{radius} ) ];

  return @points;
}

# -------------------------------------------------------------------
sub bezier_middle {
  my @control_points = @_;
  my $bezier         = Math::Bezier->new(@control_points);
  return $bezier->point(0.5);
}

# -------------------------------------------------------------------
sub bezier_points {
  #
  # given a list of control points for a bezier curve, return
  # $CONF{beziersamples}
  # points on the curve as a list
  #
  # ( [x1,y1], [x2,y2], ... )
  #
  my @control_points = @_;
  my $bezier         = Math::Bezier->new(@control_points);
  my @points         = $bezier->curve( $CONF{beziersamples} );
  my @bezier_points;
  while (@points) {
    push @bezier_points, [ splice( @points, 0, 2 ) ];
  }
  return @bezier_points;
}

# -------------------------------------------------------------------
sub bezier_control_points {
  validate(
	   @_,
	   {
            pos1                  => 1,
            chr1                  => 1,
            radius1               => 1,
            pos2                  => 1,
            chr2                  => 1,
            radius2               => 1,
            bezier_radius         => 1,
            perturb_bezier_radius => 0,

            bezier_radius_purity         => 0,
            perturb_bezier_radius_purity => 0,

            crest         => 0,
            perturb_crest => 0,
	   }
	  );
  my %params = @_;

  $params{bezier_radius} = unit_parse( $params{bezier_radius} );

  my ( $a1, $a2 ) = (
		     getanglepos( $params{pos1}, $params{chr1} ),
		     getanglepos( $params{pos2}, $params{chr2} )
		    );
  my ( $x1, $y1 ) = getxypos( $a1, $params{radius1} );
  my ( $x2, $y2 ) = getxypos( $a2, $params{radius2} );
  my $bisecting_radius =
    sqrt( ( ( $x1 + $x2 ) / 2 - $DIMS->{image}{width} / 2 )**2 +
          ( ( $y1 + $y2 ) / 2 - $DIMS->{image}{height} / 2 )**2 );

  my $middleangle = abs( $a2 - $a1 ) > 180
    ? ( $a1 + $a2 + 360 ) / 2 - 360
      : ( $a2 + $a1 ) / 2;

  if ( defined $params{bezier_radius_purity} ) {
    my $k = $params{bezier_radius_purity};
    $k = perturb_value( $k, $params{perturb_bezier_radius_purity} );
    my $x =
      abs( 1 - $k ) * abs( $params{bezier_radius} - $bisecting_radius );

    if ( $params{bezier_radius} > $bisecting_radius ) {
      if ( $k > 1 ) {
	$params{bezier_radius} = $params{bezier_radius} + $x;
      } else {
	$params{bezier_radius} = $params{bezier_radius} - $x;
      }
    } else {
      if ( $k > 1 ) {
	$params{bezier_radius} = $params{bezier_radius} - $x;
      } else {
	$params{bezier_radius} = $params{bezier_radius} + $x;
      }
    }
  }

  $params{bezier_radius} = perturb_value( 
					 $params{bezier_radius}, $params{perturb_bezier_radius} 
					);

  my ( $x3, $y3 ) = getxypos( $middleangle, $params{bezier_radius} );

  # add intermediate points if crests are requested
  my @controlpoints = ( $x1, $y1, $x3, $y3, $x2, $y2 );

  if ( defined $params{crest} ) {
    $params{crest} =
      perturb_value( $params{crest}, $params{perturb_crest} );
    my $crest_radius;

    if ( $params{radius1} > $params{bezier_radius} ) {
      $crest_radius =
	$params{radius1} -
	  abs( $params{radius1} - $params{bezier_radius} ) * $params{crest};
    } else {
      $crest_radius =
	$params{radius1} +
	  abs( $params{radius1} - $params{bezier_radius} ) * $params{crest};
    }

    splice( @controlpoints, 2, 0, getxypos( $a1, $crest_radius ) );

    if ( $params{radius2} > $params{bezier_radius} ) {
      $crest_radius =
	$params{radius2} -
	  abs( $params{radius2} - $params{bezier_radius} ) * $params{crest};
    } else {
      $crest_radius =
	$params{radius2} +
	  abs( $params{radius2} - $params{bezier_radius} ) * $params{crest};
    }
    splice( @controlpoints, 6, 0, getxypos( $a2, $crest_radius ) );
  }

  return @controlpoints;
}

# -------------------------------------------------------------------
sub ribbon {
  validate(
	   @_,
	   {
            image                        => { isa => 'GD::Image' },
            start1                       => 1,
            end1                         => 1,
            chr1                         => 1,
            start2                       => 1,
            end2                         => 1,
            chr2                         => 1,
            radius1                      => 1,
            radius2                      => 1,
            edgecolor                    => 1,
            edgestroke                   => 1,
            fillcolor                    => 0,
            bezier_radius                => 0,
            perturb_bezier_radius        => 0,
            bezier_radius_purity         => 0,
            perturb_bezier_radius_purity => 0,
            crest                        => 0,
            perturb_crest                => 0,
            mapoptions                   => { type => HASHREF, optional => 1 },
	   }
	  );
  my %params = @_;

  if ($SVG_MAKE) {
    my @path;
    my $angle1_start = getanglepos( $params{start1}, $params{chr1} );
    my $angle1_end   = getanglepos( $params{end1},   $params{chr1} );
    my $angle2_start = getanglepos( $params{start2}, $params{chr2} );
    my $angle2_end   = getanglepos( $params{end2},   $params{chr2} );

    my @bezier_control_points1 = (
				  bezier_control_points(
							pos1                  => $params{end1},
							chr1                  => $params{chr1},
							pos2                  => $params{end2},
							chr2                  => $params{chr2},
							radius1               => $params{radius1},
							radius2               => $params{radius2},
							bezier_radius         => $params{bezier_radius},
							perturb_bezier_radius => $params{perturb_bezier_radius},
							bezier_radius_purity  => $params{bezier_radius_purity},
							perturb_bezier_radius_purity =>
							$params{perturb_bezier_radius_purity},
							crest         => $params{crest},
							perturb_crest => $params{perturb_crest},
						       )
				 );

    my @bezier_control_points2 = (
				  bezier_control_points(
							pos1                  => $params{start2},
							chr1                  => $params{chr2},
							pos2                  => $params{start1},
							chr2                  => $params{chr1},
							radius1               => $params{radius2},
							radius2               => $params{radius1},
							bezier_radius         => $params{bezier_radius},
							perturb_bezier_radius => $params{perturb_bezier_radius},
							bezier_radius_purity  => $params{bezier_radius_purity},
							perturb_bezier_radius_purity =>
							$params{perturb_bezier_radius_purity},
							crest         => $params{crest},
							perturb_crest => $params{perturb_crest},
						       )
				 );

    push @path,
      sprintf( "M %.3f,%.3f", getxypos( $angle1_start, $params{radius1} ) );

    push @path, sprintf(
			"A %.3f,%.3f %.2f %d,%d %.1f,%.1f",
			$params{radius1},
			$params{radius1},
			0,
			abs( $angle1_start - $angle1_end ) > 180,
			$angle1_start < $angle1_end,
			getxypos( $angle1_end, $params{radius1} )
		       );

    if ( @bezier_control_points1 == 10 ) {
      my @bezier_points = bezier_points(@bezier_control_points1);
      my $point_string  = "%.1f,%.1f " x @bezier_points;
      push @path,
	sprintf( "L $point_string",
		 ( map { @$_ } @bezier_points[ 0 .. @bezier_points - 1 ] ) );
    } elsif ( @bezier_control_points1 == 8 ) {
      my $point_string = join( $SPACE,
			       map { sprintf( "%.1f", $_ ) }
			       @bezier_control_points1[ 2 .. @bezier_control_points1 - 1 ] );
      push @path, sprintf( "C %s", $point_string );
    } elsif ( @bezier_control_points1 == 6 ) {
      push @path,
	sprintf( "Q %.1f,%.1f %.1f,%.1f",
		 @bezier_control_points1[ 2 .. @bezier_control_points1 - 1 ] );
    }

    push @path, sprintf(
			"A %.3f,%.3f %.2f %d,%d %.1f,%.1f",
			$params{radius2},
			$params{radius2},
			0,
			abs( $angle2_start - $angle2_end ) > 180,
			$angle2_start > $angle2_end,
			getxypos( $angle2_start, $params{radius2} )
		       );

    if ( @bezier_control_points2 == 10 ) {
      my @bezier_points = bezier_points(@bezier_control_points2);
      my $point_string  = "%.1f,%.1f " x @bezier_points;
      push @path,
	sprintf( "L $point_string",
		 ( map { @$_ } @bezier_points[ 0 .. @bezier_points - 1 ] ) );
    } elsif ( @bezier_control_points2 == 8 ) {
      my $point_string = join( $SPACE,
			       map { sprintf( "%.1f", $_ ) }
			       @bezier_control_points2[ 2 .. @bezier_control_points2 - 1 ] );
      push @path, sprintf( "C %s", $point_string );
    } elsif ( @bezier_control_points2 == 6 ) {
      push @path,
	sprintf( "Q %.1f,%.1f %.1f,%.1f",
		 @bezier_control_points2[ 2 .. @bezier_control_points2 - 1 ] );
    }
    push @path, "Z";

    my $svg_colors;
    if ( $params{edgecolor} ) {
      $svg_colors .= sprintf( qq{ stroke: rgb(%d,%d,%d);},
			      rgb_color( $params{edgecolor} ) );
    }

    if ( $params{fillcolor} && rgb_color($params{fillcolor}) ) {
      $svg_colors .= sprintf( qq{ fill: rgb(%d,%d,%d);},
			      rgb_color( $params{fillcolor} ) );
      if ( rgb_color_opacity( $params{fillcolor} ) < 1 ) {
	$svg_colors .= sprintf( qq{ opacity: %.3f;},
				rgb_color_opacity( $params{fillcolor} ) );
      }
    }

    my $svg = sprintf(
		      qq{<path d="%s" style="stroke-width: %.1f; %s"/>},
		      join( $SPACE, @path ),
		      $params{edgestroke}, $svg_colors,
		     );

    printsvg($svg);

  }

  if ($PNG_MAKE) {
    my $poly = GD::Polygon->new;

    # arc along span 1
    my @points = arc_points(
			    start  => $params{start1},
			    end    => $params{end1},
			    chr    => $params{chr1},
			    radius => $params{radius1}
			   );

    # bezier from span1 to span2
    push @points, bezier_points(
				bezier_control_points(
						      pos1                  => $params{end1},
						      chr1                  => $params{chr1},
						      pos2                  => $params{end2},
						      chr2                  => $params{chr2},
						      radius1               => $params{radius1},
						      radius2               => $params{radius2},
						      bezier_radius         => $params{bezier_radius},
						      perturb_bezier_radius => $params{perturb_bezier_radius},
						      bezier_radius_purity  => $params{bezier_radius_purity},
						      perturb_bezier_radius_purity =>
						      $params{perturb_bezier_radius_purity},
						      crest         => $params{crest},
						      perturb_crest => $params{perturb_crest},
						     )
			       );

    # arc along span 2
    push @points, arc_points(
			     start  => $params{end2},
			     end    => $params{start2},
			     chr    => $params{chr2},
			     radius => $params{radius2}
			    );

    push @points, bezier_points(
				bezier_control_points(
						      pos1                  => $params{start2},
						      chr1                  => $params{chr2},
						      pos2                  => $params{start1},
						      chr2                  => $params{chr1},
						      radius1               => $params{radius2},
						      radius2               => $params{radius1},
						      bezier_radius         => $params{bezier_radius},
						      perturb_bezier_radius => $params{perturb_bezier_radius},
						      bezier_radius_purity  => $params{bezier_radius_purity},
						      perturb_bezier_radius_purity =>
						      $params{perturb_bezier_radius_purity},
						      crest         => $params{crest},
						      perturb_crest => $params{perturb_crest},
						     )
			       );

    for my $point (@points) {
      $poly->addPt(@$point);
    }

    if ( defined $params{fillcolor} && $COLORS->{ $params{fillcolor} } ) {
      $IM->filledPolygon( $poly, aa_color($params{fillcolor},$IM,$COLORS) );
    } else {
      # not filling
    }

    # stroke the polygon, if required
    if ( $params{edgestroke} ) {
      my $thickness = $params{edgestroke};
      my $color     = $params{edgecolor};
      my $line_color_obj;
      if($thickness == 1 && rgb_color_opacity($color) == 1) {
	# this is a 1-px thick line and the color has no transparency - 
	# go ahead and antialias this line
	$IM->setAntiAliased($COLORS->{$color});
	$line_color_obj = gdAntiAliased;
      } else {
	$IM->setThickness($thickness) if $thickness > 1;
	$line_color_obj = $COLORS->{$color};
      }
      $IM->polygon( $poly, $line_color_obj );
      $IM->setThickness(1) if $thickness > 1;
    }

    # contribute to image map
    if(defined $params{mapoptions}{url}) {
      my $xshift = $CONF{image}{image_map_xshift}||0;
      my $yshift = $CONF{image}{image_map_xshift}||0;
      my $xmult  = $CONF{image}{image_map_xfactor}||1;
      my $ymult  = $CONF{image}{image_map_yfactor}||1;
      my @coords = map { ( $_->[0]*$xmult + $xshift , $_->[1]*$ymult + $yshift ) } $poly->vertices;
      report_image_map(shape=>"poly",
		       coords=>\@coords,
		       href=>$params{mapoptions}{url});
    }
  }
}

{
  my $sliceid = 0;
  # -------------------------------------------------------------------
  sub slice {
    validate(
	     @_,
	     {
	      image        => { isa => 'GD::Image' },
	      start        => 1,
	      start_offset => 0,
	      end_offset   => 0,
	      end          => 1,
	      chr          => 1,
	      radius_from  => 1,
	      radius_to    => 1,
	      edgecolor    => 1,
	      edgestroke   => 1,
	      fillcolor    => 0,
	      ideogram     => 0,
	      mapoptions => { type => HASHREF, optional => 1 },
	     }
	    );
    my %params = @_;

    # determine whether to draw this slice, or whether it is only being
    # used to define an image map element. A slice that appears in the image
    # must have one of edge color, edge stroke or fill color defined.
    my $draw_slice = 
      defined $params{edgecolor} || 
	defined $params{edgestroke} ||
	  defined $params{fillcolor};
    
    my ( $start_a, $end_a ) = (
			       getanglepos( $params{start}, $params{chr} ),
			       getanglepos( $params{end},   $params{chr} )
			      );

    #printdumper(\%params,$start_a,$end_a);

    if ( $end_a < $start_a ) {
      ( $start_a, $end_a ) = ( $end_a, $start_a );
    }

    # The offsets are used to accomodate scales for very short ideograms
    # where individual base positions need to be identified. It allows 
    # elements with start=end to be drawn without collapsing into a very
    # thin slice, where start/end angles are the same.
    my @offsets = $CONF{offsets} ? split(",",$CONF{offsets}) : (1,1);
    $params{start_offset} = $offsets[0] if !defined $params{start_offset};
    $params{end_offset}   = $offsets[1] if !defined $params{end_offset};

    $start_a -= 360 * $params{start_offset} / $GCIRCUM;
    $end_a += 360 * $params{end_offset} / $GCIRCUM;

    my $angle_orientation = $CONF{image}{angle_orientation} || $EMPTY_STR;
    if ( $angle_orientation eq 'counterclockwise' ) {
      ( $start_a, $end_a ) = ( $end_a, $start_a ) if $end_a < $start_a;
    } else {
      $start_a -= 360 if $start_a > $end_a;
    }

    my $svg;
    if ( $params{radius_from} == $params{radius_to} ) {
      my $end_a_mod = $end_a;
      if ( abs( $end_a - $start_a ) > 359.99 || $start_a == $end_a ) {
	$end_a_mod -= 0.01;
      }
      #
      # when the start/end radius is the same, there can be no
      # fill because the slice is 0-width
      #
      $svg = sprintf(
		     qq{<path d="M %.1f,%.1f A%.1f,%.1f %.2f %d,%d %.1f,%.1f" style="%s %s fill: none;" />},
		     getxypos( $start_a, $params{radius_from} ),
		     $params{radius_from},
		     $params{radius_from},
		     0,
		     abs( $start_a - $end_a_mod ) > 180,
		     1,
		     getxypos( $end_a_mod, $params{radius_from} ),
		     $params{edgestroke}
		     ? sprintf( "stroke-width: %.1f;", $params{edgestroke} )
		     : "stroke: none;",
		     $params{edgestroke}
		     && $params{edgecolor} ? sprintf( "stroke: rgb(%d,%d,%d);",
						      rgb_color( $params{edgecolor} ) ) : $EMPTY_STR,
		    );
    } elsif ( $end_a == $start_a ) {
      $svg = sprintf(
		     qq{<path d="M %.1f,%.1f L %.1f,%.1f " style="%s %s fill: none;" />},
		     getxypos( $start_a, $params{radius_from} ),
		     getxypos( $end_a,   $params{radius_to} ),
		     $params{edgestroke}
		     ? sprintf( "stroke-width: %.1f;", $params{edgestroke} )
		     : "stroke: none;",
		     $params{edgestroke}
		     && $params{edgecolor} ? sprintf( "stroke: rgb(%d,%d,%d);",
						      rgb_color( $params{edgecolor} ) ) : $EMPTY_STR,
		    );
    } else {
      my $sweepflag = abs( $start_a - $end_a ) > 180;
      my $end_a_mod = $end_a;
      if ( abs( $end_a - $start_a ) > 359.99 || $start_a == $end_a ) {
	$end_a_mod -= 0.01;
      }

      $svg = sprintf(
		     qq{<path d="M %.3f,%.3f A%.3f,%.3f %.3f %d,%d %.3f,%.3f L %.3f,%.3f A%.3f,%.3f %.3f %d,%d %.3f,%.3f Z " style="%s %s %s %s" />},
		     getxypos( $start_a, $params{radius_from} ),
		     $params{radius_from}, $params{radius_from},
		     0,
		     $sweepflag, 1,
		     getxypos( $end_a_mod, $params{radius_from} ),
		     getxypos( $end_a_mod, $params{radius_to} ),
		     $params{radius_to}, $params{radius_to},
		     0,
		     $sweepflag, 0,
		     getxypos( $start_a, $params{radius_to} ),
		     $params{edgestroke}
		     ? sprintf( "stroke-width: %.1f;", $params{edgestroke} )
		     : "stroke: none;",
		     $params{edgestroke} && $params{edgecolor} 
		     ? sprintf( 
			       "stroke: rgb(%d,%d,%d);", 
			       rgb_color( $params{edgecolor} ) 
			      ) 
		     : $EMPTY_STR,
		     $params{fillcolor} 
		     ? sprintf( "fill: rgb(%d,%d,%d);",
				rgb_color( $params{fillcolor} ) 
			      ) 
		     : 'fill: none;',
		     rgb_color_opacity( $params{fillcolor} ) < 1
		     ? sprintf( "opacity: %.3f;",
				rgb_color_opacity( $params{fillcolor} ) )
		     : $EMPTY_STR,
		    );
    }

    printsvg($svg) if $draw_slice;

    my $poly;
    if ( $params{radius_from} != $params{radius_to} ) {
      $poly = GD::Polygon->new;
    } else {
      $poly = GD::Polyline->new;
    }

    my ( $x, $y, $xp, $yp ) = (0,0,0,0);
    for (
	 my $angle = $start_a;
	 $angle   <= $end_a;
	 $angle   += $CONF{anglestep}
        ) {
      ( $x, $y ) = getxypos( $angle, $params{radius_from} );
      my $d = sqrt( ( $x - $xp )**2 + ( $y - $yp )**2 );
      next if $xp && $yp && $d < $CONF{minslicestep};
      $poly->addPt( $x, $y );
      ( $xp, $yp ) = ( $x, $y );
    }

    if ( $end_a != $start_a ) {
      $poly->addPt( getxypos( $end_a, $params{radius_from} ) );
    }

    if ( $params{radius_from} != $params{radius_to} ) {
      ( $xp, $yp ) = ( 0,0 );
      for (
	   my $angle = $end_a;
	   $angle    > $start_a;
	   $angle   -= $CONF{anglestep}
	  ) {
	( $x, $y ) = getxypos( $angle, $params{radius_to} );
	my $d = sqrt( ( $x - $xp )**2 + ( $y - $yp )**2 );
	next if $xp && $yp && $d < $CONF{minslicestep};
	$poly->addPt( getxypos( $angle, $params{radius_to} ) );
	( $xp, $yp ) = ( $x, $y );
      }

      $poly->addPt( getxypos( $start_a, $params{radius_to} ) );
    }

    # fill the polygon if desired
    if ( $draw_slice
	 && defined $params{fillcolor}
	 && ref $poly eq "GD::Polygon"
	 && $PNG_MAKE
       ) {
      $IM->setAntiAliased($COLORS->{ $params{fillcolor}});
      $IM->filledPolygon( $poly, gdAntiAliased );
    }

    # stroke the polygon
    if ( $draw_slice && $params{edgestroke} ) {
      my $thickness = $params{edgestroke};
      my $color     = $params{edgecolor} || $params{fillcolor};
      my $line_color_obj;
      if($thickness == 1 && rgb_color_opacity($color) == 1) {
	# this is a 1-px thick line and the color has no transparency - 
	# go ahead and antialias this line
	$IM->setAntiAliased($COLORS->{$color});
	$line_color_obj = gdAntiAliased;
      } else {
	$IM->setThickness($thickness) if $thickness > 1;
	$line_color_obj = $COLORS->{$color};
      }
      if ( ref $poly eq "GD::Polygon" ) {
	$IM->polygon( $poly, $line_color_obj ) if $PNG_MAKE;
      } else {
	$IM->polydraw( $poly, $line_color_obj ) if $PNG_MAKE;
      }
      $IM->setThickness(1) if $thickness > 1;
    }
    $sliceid++;

    # contribute to image map
    if(defined $params{mapoptions}{url}) {
      my $xshift = $CONF{image}{image_map_xshift}||0;
      my $yshift = $CONF{image}{image_map_xshift}||0;
      my $xmult  = $CONF{image}{image_map_xfactor}||1;
      my $ymult  = $CONF{image}{image_map_yfactor}||1;
      my @coords = map { ( $_->[0]*$xmult + $xshift , $_->[1]*$ymult + $yshift ) } $poly->vertices;
      report_image_map(shape=>"poly",
		       coords=>\@coords,
		       href=>$params{mapoptions}{url});
    }
  }
}

sub report_image_map {
  # given a shape, coordinates (as a list) and an href string, report
  # an element of the image map
  my %args = @_;
  my $href = $args{href};
  if($href =~ /^[^\/]+\/\//) {
    # protocol found
  } elsif(defined $CONF{image}{image_map_protocol}) {
    # prefix the url with the protocol, if defined
    $href = sprintf("%s://%s",$CONF{image}{image_map_protocol},$href);
  }
  my $map_string = sprintf ("<area shape='%s' coords='%s' href='%s' alt='%s' title='%s'>\n",
			    $args{shape},
			    join(",",map {round($_)} @{$args{coords}}),
			    $href,
			    $href,
			    $href,
			   );
  push @MAP_ELEMENTS, {string=>$map_string,
		       type=>$args{shape},
		       coords=>$args{coords}};
}

# -------------------------------------------------------------------
sub myarc {
  my ( $im, $c, $radius, $a1, $a2, $color ) = @_;

  my $astep = 0.1 / $radius * 180 / $PI;
  $astep    = max( 0.01, $astep );

  for ( my $a = $a1 ; $a <= $a2 ; $a += $astep ) {
    $im->setPixel( getxypos( $a, $radius ), $color ) if $PNG_MAKE;
  }
}

# -------------------------------------------------------------------
sub getxypos {
  #
  # given an angle, get the xy position for a certain radius
  #
  # return float
  #

  return (
	  $DIMS->{image}{radius} + $_[1] * cos( $_[0] * $DEG2RAD ),
	  $DIMS->{image}{radius} + $_[1] * sin( $_[0] * $DEG2RAD )
	 );
}

# -------------------------------------------------------------------
sub getrdistance {
  my ( $pos, $chr, $r ) = @_;
  my $d;

  if ( $CONF{image}{angle_orientation} eq "counterclockwise" ) {
    $d =
      $r *
	$DEG2RAD * 360 *
          ( 1 - getrelpos_scaled( $pos, $chr ) / $GCIRCUM );
  } else {
    $d = $r * $DEG2RAD * 360 * getrelpos_scaled( $pos, $chr ) / $GCIRCUM;
  }

  return $d;
}

# Get the angle for a given sequence position within the genome,
# with appropriate padding built in
#
# return in degrees
sub getanglepos {
  my ( $pos, $chr ) = @_;
  my $angle;
  if ( 
      defined $CONF{image}{angle_orientation} 
      &&
      $CONF{image}{angle_orientation} eq "counterclockwise" 
     ) {
    $angle = 360 * ( 1 - getrelpos_scaled( $pos, $chr ) / $GCIRCUM );
  } else {
    $angle = 360 * getrelpos_scaled( $pos, $chr ) / $GCIRCUM;
  }

  if ( $CONF{image}{angle_offset} ) {
    $angle += $CONF{image}{angle_offset};
    # bugfix v0.40 - take care of any multiple of 360
    $angle -= 360 * int( $angle / 360 ) if $angle > 360;
  }
  printdebug( "getanglepos", $pos, $chr, $angle );
  return $angle;
}

# -------------------------------------------------------------------
sub get_ideogram_idx {
  # given a chromosome and base pair position, return the index
  # of the ideogram where the position is found
  my ( $pos, $chr ) = @_;
  for my $ideogram (@IDEOGRAMS) {
    if ( $ideogram->{chr} eq $chr && $ideogram->{set}->member($pos) ) {
      return $ideogram->{idx};
    }
  }

  return undef;
}

# -------------------------------------------------------------------
sub get_ideogram_by_idx {
  my $idx = shift;
  my ($ideogram) = grep( $_->{idx} == $idx, @IDEOGRAMS );
  if ($ideogram) {
    return $ideogram;
  } else {
    confess "consistency error in get_ideogram_by_idx - ",
      "no ideogram with index $idx exists";
  }
}

# -------------------------------------------------------------------
sub getrelpos_scaled_ideogram_start {
  my $ideogram_idx = shift;
  my $pos          = 0;
  for my $ideogram (@IDEOGRAMS) {
    my $idx = $ideogram->{idx};
    if ( $idx == $ideogram_idx ) {

      # individual ideograms can be reversed - v0.48
      if ( $ideogram->{reverse} ) {
	$pos += $ideogram->{length}{scale};
      }

      last;
    }

    $pos += $ideogram->{length}{scale};

    if ( $ideogram->{next} ) {
      my $x = ideogram_spacing( $ideogram, $ideogram->{next} );
      $pos += $x;
    }
  }

  return $pos;
}

# -------------------------------------------------------------------
sub getrelpos_scaled {
  #
  # relative position around the circle [0,1] for a given base
  # position and chromosome.
  #
  my ( $pos, $chr ) = @_;
  my $ideogram_idx = get_ideogram_idx( $pos, $chr );
  my $relpos       = getrelpos_scaled_ideogram_start($ideogram_idx);
  my $ideogram     = get_ideogram_by_idx($ideogram_idx);
  if ( $ideogram->{chr} eq $chr && $ideogram->{set}->member($pos) ) {
    my $direction = $ideogram->{reverse} ? -1 : 1;
    for my $cover ( @{ $ideogram->{covers} } ) {
      if ( $cover->{set}->member($pos) ) {

	# found the cover that has the position we seek
	$relpos +=
	  $direction * ( $pos - $cover->{set}->min ) * $cover->{scale};

	return $relpos;
      } else {
	$relpos +=
	  $direction * $cover->{set}->cardinality * $cover->{scale};
      }
    }
    confess "error - consistency problem in getrelpos_scaled - ",
      "ideogram exhausted ($pos,$chr)";
  }

  return $relpos;
}

# -------------------------------------------------------------------
sub get_set_middle {
  my $set = shift;
  return ( $set->min + $set->max ) / 2;
}

# -------------------------------------------------------------------
sub text_label_size {
  #
  # return the width and height of a label, based on
  # bounds reported by GD's stringFT
  #
  # bugfix v0.40 - added this wrapper function
  #

  my @bounds = @_;
  my ( $w, $h );
  if ( $bounds[1] == $bounds[3] ) {
    $w = abs( $bounds[2] - $bounds[0] ) - 1;
    $h = abs( $bounds[5] - $bounds[1] ) - 1;
  } else {
    $w =
      sqrt( ( abs( $bounds[2] - $bounds[0] ) - 1 )**2 +
	    ( abs( $bounds[3] - $bounds[1] ) - 1 )**2 );
    $h =
      sqrt( ( abs( $bounds[6] - $bounds[0] ) - 1 )**2 +
	    ( abs( $bounds[7] - $bounds[1] ) - 1 )**2 );
  }

  return ( $w, $h );
}

# -------------------------------------------------------------------
sub textoffset {
  #
  # Drawing text with baseline parallel to radius requires that the
  # angle position be offset to maintain alignment of text to the
  # desired angle position. To make the centerline of the text align
  # with the desired text position, the text angle is offset (-'ve)
  # by an appropriate amount.
  #
  # The input angle is the angular position of the text, not the
  # angle to which the text is rotated.
  #
  # returns the appropriate angle/radius correction
  # - delta_angle
  # - delta_radius

  my ( $angle, $radius, $label_width, $label_height, $height_offset, $is_parallel ) = @_;

  my $angle_offset  = $RAD2DEG * ( ( $label_height / 2 + $height_offset ) / $radius );
  my $radius_offset = $label_width - 1;
  $angle = anglemod($angle);
  if($is_parallel) {
    if ($angle < 0 ) {
      $radius_offset = 0;
    } elsif ($angle > 0 && $angle < 180) {
      $radius_offset = $label_height;
    } else {
      $radius_offset = 0;
    }
  }
  # bug fix v0.40, >= <= changed to < >
  if ( $angle > 90 && $angle < 270 ) {
    return ( -$angle_offset, $radius_offset );
  } else {
    return ( $angle_offset, !$is_parallel ? 0 : $radius_offset );
  }
}

# -------------------------------------------------------------------
sub anglemod {
  #
  # Given an an angle, return the angle of rotation of corresponding
  # text label. The angle is adjusted so that text is always
  # right-side up.
  #
  # The angle is purposed for text rotation using GD's stringFT.
  #
  # SVG rotates text in the opposite direction from GD, and this is
  # handled elsewhere.
  #
  my $angle = shift;

  if ( $angle < 0 ) {
    $angle += 360;
  } elsif ( $angle > 360 ) {
    $angle -= 360;
  }

  return $angle;
}

################################################################
# Given an angle, determine the rotation of text that will make
# the text perpendicular to the angle.
#
# If $rotate=1, then the text will be parallel to the angle.
#
sub textangle {
  my ($angle,$is_parallel) = @_;
  $angle = anglemod($angle);
  my $textangle;
  if ( $angle <= 90 ) {
    $textangle = 360 - $angle;
  } elsif ( $angle < 180 ) {
    $textangle = 180 - $angle;
  } elsif ( $angle < 270 ) {
    $textangle = 360 - ( $angle - 180 );
  } else {
    $textangle = 360 - $angle;
  }
  if($is_parallel) {
    # v0.52 if the ideogram label is to be parallel to the ideogram by setting
    # label_parallel = yes
    # then the text direction is adjusted    
    my $oldtextangle = $textangle;
    if($oldtextangle <= 90 && $oldtextangle >= 0) {
      $textangle -= 90;
    } elsif ($oldtextangle >= 270) {
      $textangle += 90;
    }
  }
  return $textangle;
}

# -------------------------------------------------------------------
sub textanglesvg {
  my ($angle,$is_parallel) = @_;

  #$angle = $angle % 360;
  my $svgangle = 360 - textangle($angle,$is_parallel);

  #$svgangle += 0.01 if $svgangle == 90;
  return $svgangle;
}

# -------------------------------------------------------------------
sub inittracks {
  my $num = shift;
  my $tracks = [ map { Set::IntSpan->new() } ( 0 .. $num - 1 ) ];
  return $tracks;
}

# -------------------------------------------------------------------
sub gettack {
  # Given an interval set ($set) and a list of existing tracks
  # ($tracks), return the track which can accomodate the $set when
  # padded by $padding
  my $set     = shift;
  my $padding = shift;
  my $chr     = shift;
  my $tracks  = shift;
  my $scale   = shift;

  my $chr_offset = 0;
  $scale ||= 1e3;
  $chr_offset = $KARYOTYPE->{$chr}{chr}{length_cumul} if $chr;
  my $padded_set = Set::IntSpan->new(
				     sprintf( "%d-%d",
					      ( $chr_offset + $set->min - $padding ) / $scale,
					      ( $chr_offset + $set->max + $padding ) / $scale )
				    );

  for my $idx ( 0 .. @$tracks - 1 ) {
    my $thistrack = $tracks->[$idx];

    if ( !$thistrack->intersect($padded_set)->cardinality ) {
      $tracks->[$idx] = $thistrack->union($padded_set);
      return $idx;
    }
  }

  return undef;
}

# -------------------------------------------------------------------
sub parse_options {
  #
  # parse option string like
  #
  # var1=value1,var2=value2,...
  #
  # into a hash
  validate( @_, { string => 1 } );
  my %params = @_;
  my $string = $params{string} || $EMPTY_STR;
  my $options;

  my @option_pairs = split(/,/,$string);
  for my $option_pair ( @option_pairs ) {
    if($option_pair =~ /^([^=]+)=(.+)$/) {
      $options->{$1} = $2;
    }
  }

  #for my $option_pair ( split( /,/, $string ) ) {
  #  my ( $option, $value ) = split( /=/, $option_pair );
  #  if ( defined $option && defined $value ) {
  #    $options->{$option} = $value;
  #  }
  #}
  
  return $options;
}

sub is_number {
  my $text = shift;
  return $text =~ /^[-+]?[0-9]*\.?[0-9]+([eE][-+]?[0-9]+)?$/;
}

sub is_blank {
  my $string = shift;
  return $string =~ /^\s*$/;
}

sub is_comment {
  my $string = shift;
  return $string =~ /^\s*\#/;
}

################################################################
# Read the karyotype file and parsed chromosome and band locations.
#
# Chromosomes have the format
#
# chr - hs1 1 0 247249719 green
# chr - hs2 2 0 242951149 green
#
# and bands
#
# band hs1 p36.33 p36.33 0 2300000 gneg
# band hs1 p36.32 p36.32 2300000 5300000 gpos25
#
# The fields are
#
# field parent name label start end color options
#
# Note that name and label can be different. The label (e.g. 1) is what appears
# on the image, but the name (e.g. hs1) is what is used in the input data file.
#
# v0.52 - additional error checks and tidying
#
sub read_karyotype {
  validate( @_, { file => 1 } );
  my %params = @_;
  $params{file} = locate_file( file => $params{file} );
  my $karyotype;
  my $chr_index = 0; # keep track of the number of chromosome records in the file
  open( F, $params{file} ) or confess "Cannot open $params{file}\n";
  while (<F>) {
    chomp;
    next if is_blank($_);
    next if is_comment($_);
    my ( $field, $parent, $name, $label, $start, $end, $color, $options ) =
      $CONF{file_delim} ? split($CONF{file_delim}) : split;

    if ( ! is_number($start) || ! is_number($end) ) {
      confess "fatal error - start/end coordinates in karyotype are not digits ($start,$end)";
    }
    if ( $end <= $start ) {
      confess "fatal error - end coordinate in karyotype is same or lower than start ($start,$end)";
    }

    my $set  = newspan($start,$end); #Set::IntSpan->new("$start-$end");

    # karyotype data structure is a hash with each chromosome being a value
    # keyed by chromosome name. Bands form a list within the chromosome
    # data structure, keyed by 'band'.

    my $data = {
		start   => $start,
		end     => $end,
		set     => $set,
		size    => $set->cardinality,
		parent  => $parent,
		name    => $name,
		label   => $label,
		color   => lc $color,
		options => parse_options( string => $options )
	       };

    if ( $field =~ /chr/ ) {
      # chromosome entries have a few additional fields
      # chr, scale, display_order
      $data->{chr}           = $name;
      $data->{scale}         = 1;
      $data->{display_order} = $chr_index++;
      if ( $karyotype->{$data->{chr}}{chr} ) {
	confess "fatal error - you have defined chromosome $data->{chr} twice in the karyotype file";
      }
      # chromosome is keyed by its name
      $karyotype->{ $name }{chr} = $data;
    } elsif ( $field =~ /band/ ) {
      # band entries have the 'chr' key point to the name of parent chromosome
      $data->{chr} = $parent;
      if ( ! $karyotype->{$parent}{chr} ) {
	# Used to quit here, but now this function is in validate_karyotype. This change was done so that 
	# you may define a band for a chromosome before the chromosome itself.
	#confess "fatal error - you've defined bands for chromosome $parent but this chromosome itself has not been first defined.";
      }
      push @{ $karyotype->{ $parent }{band} }, $data;
    } else {
      # for now, die hard here. There are no other line types supported.
      confess "fatal error - you have a field line named $field in the karyotype file. Currently only 'chr' or 'band' are supported.";
      #push @{ $karyotype->{$parent}{$field} }, $data;
    }
  }
  return $karyotype;
}

################################################################
#
# Verify the contents of the karyotype data structure. Basic
# error checking also happens in read_karyotype (above). Here,
# we perform more detailed diagnostics.
#
# The following are checked
# 
# error  condition
# FATAL  a band has no associated chromosome
# FATAL  band coordinates extend outside chromosome
# FATAL  two bands overlap by more than max_band_overlap
# WARN   a chromosome has a parent field definition
# WARN   bands do not completely cover the chromosome

sub validate_karyotype {
  validate( @_, { karyotype => 1 } );
  my %params    = @_;
  my $karyotype = $params{karyotype};
  for my $chr ( keys %$karyotype ) {
    if ( !$karyotype->{$chr}{chr} ) {
      confess "error - you've defined structures on chromsome ",
	"$chr but have no definition for the chromosome itself ",
	  "(is there a 'chr' line for this chromosome in the ",
            "karyotype file?";
    }
    if ( $karyotype->{$chr}{chr}{parent} ne $DASH ) {
      printwarning( 
		   "chromosome $chr has a parent field - ",
		   "chromosome parents are not currently supported"
		  );
    }

    my $chrset           = $karyotype->{$chr}{chr}{set};
    my $bandcoverage     = Set::IntSpan->new();
    # Bands can overlap by at most this many bases.
    my $max_band_overlap = 1;

    for my $band ( make_list( $karyotype->{$chr}{band} ) ) {
      if ( $band->{set}->diff($chrset)->cardinality ) {
	confess "band $band->{name} on chromosome $chr has ",
	  "coordinates that extend outside chromosome";
      } elsif ( $band->{set}->intersect($bandcoverage)->cardinality > $max_band_overlap ) {
	confess "band $band->{name} overlaps with another band by ",
	  "more than $max_band_overlap base on chromosome $chr";
      }
      $bandcoverage = $bandcoverage->union( $band->{set} );
    }
    if ($bandcoverage->cardinality && $bandcoverage->cardinality < $chrset->cardinality ) {
      printwarning("bands for chromosome $chr do not cover entire chromosome");
    }
  }
}

# -------------------------------------------------------------------
sub locate_file {
  validate( @_, { file => 1, return_undef => 0 } );
  my %params = @_;
  my $file   = $params{file};

  if ( -e $file && -r _ ) {
    return $file;
  } elsif ( -e $file && !-r _ ) {
    confess "file $file exists, but cannot be read";
  } else {
    # look for the file elsewhere
    for my $dir (
		 "$FindBin::RealBin/",       
		 "$FindBin::RealBin/etc",
		 "$FindBin::RealBin/../etc", 
		 "$FindBin::RealBin/../",
		 "$FindBin::RealBin/../etc", 
		 "$FindBin::RealBin/../../etc",
		) {
      printwarning("trying $dir/$file");
      if ( -e "$dir/$file" && -r "$dir/$file" ) {
	printwarning("$file found in $dir/$file");
	return "$dir/$file";
      }
    }
  }

  if ( $params{return_undef} ) {
    return undef;
  } else {
    confess "could not locate $file";
  }
}

# -------------------------------------------------------------------
sub add_thousands_separator {
  my $str = shift;
  my $sep = shift || $COMMA;

  if ( $str =~ /\./ ) {
    $str =~ s/(?<=\d)(?=(\d{3})+\.)/,/g;
  } else {
    $str =~ s/(?<=\d)(?=(\d{3})+$)/,/g;
  }

  return $str;
}

# -------------------------------------------------------------------
sub defined_but_zero {
  return defined $_[0] && !$_[0];
}

# -------------------------------------------------------------------
sub is_integer {
  return $_[0] == int( $_[0] );
}

# -------------------------------------------------------------------
sub show_element {
  #
  # returns true only if
  #  show parameter is not defined
  #  show parameter is defined and true
  #  hide parameter is not defined
  #  hide parameter is defined by false
  #

  my $param = shift;
  croak "input parameter is not a hash reference" unless ref($param) eq "HASH";

  # the presence of "hide" overrides any value of "show"
  return 0 if $param->{hide};
  return 1 if !exists $param->{show} || $param->{show};
  return 0;
}

# -------------------------------------------------------------------
sub debug_or_group {
  my $group = shift;
  return $CONF{debug} || $CONF{debug_group} =~ /$group/;
}

################################################################
#
# *** DO NOT EDIT BELOW THIS LINE ***
#
################################################################
################################################################
################################################################
################################################################

# -------------------------------------------------------------------
sub validateconfiguration {
  for my $parsekey ( keys %CONF ) {
    if ( $parsekey =~ /^(__(.+)__)$/ ) {
      if ( !defined $CONF{$1} ) {
	confess "ERROR - problem in configuration file - ",
	  "you want to use variable $1 ($2) in another parameter, ",
	    "but this variable is not defined";
      }

      my ( $token, $parsevalue ) = ( $1, $CONF{$1} );
      for my $key ( keys %CONF ) {
	$CONF{$key} =~ s/$token/$parsevalue/g;
      }
    }
  }

  $CONF{chromosomes_units} ||= 1;
  $CONF{svg_font_scale} ||= 1;

  if ( !$CONF{configfile} ) {
    confess "Error: no configuration file specified. Please use -conf FILE";
  }

  if ( !$CONF{karyotype} ) {
    confess "Error: no karotype file specified";
  }

  $CONF{image}{image_map_name} ||= $CONF{image_map_name};
  $CONF{image}{image_map_use}  ||= $CONF{image_map_use};
  $CONF{image}{image_map_file} ||= $CONF{image_map_file};
  $CONF{image}{image_map_missing_parameter} ||= $CONF{image_map_missing_parameter};
  $CONF{image}{"24bit"} ||= $CONF{"24bit"};
  $CONF{image}{png}   ||= $CONF{png};
  $CONF{image}{svg}   ||= $CONF{svg};

  if ( $CONF{image}{angle_offset} > 0 ) {
    $CONF{image}{angle_offset} -= 360;
  }

  #
  # Make sure these fields are initialized
  #
  for my $fld ( 
	       qw[ 
		   chromosomes chromosomes_breaks chromosomes_radius
		] 
	      ) {
    $CONF{ $fld } = $EMPTY_STR if !defined $CONF{ $fld };
  }

}

# -------------------------------------------------------------------
sub populateconfiguration {

  for my $key ( keys %OPT ) {
    $CONF{$key} = $OPT{$key};
  }

  # any configuration fields of the form __XXX__ are parsed and replaced
  # wiht eval(XXX).
  # The configuration can therefore depend on itself.
  #
  # flag = 10
  # note = __2*$CONF{flag}__ # would become 2*10 = 20

  repopulateconfiguration( \%CONF );

  # populate some defaults
  $CONF{'anglestep'}    ||= 1;
  $CONF{'minslicestep'} ||= 5;
}

# -------------------------------------------------------------------
sub repopulateconfiguration {
  my $root = shift;

  for my $key ( keys %$root ) {
    my $value = $root->{$key};
    if ( ref($value) eq 'HASH' ) {
      repopulateconfiguration($value);
    } elsif ( ref($value) eq 'ARRAY' ) {
      for my $item (@$value) {
	repopulateconfiguration($item) if ref($item);
      }
    } else {
      while ( $value =~ /__([^_].+?)__/g ) {
	my $source = "__" . $1 . "__";
	my $target = eval $1;
	$value =~ s/\Q$source\E/$target/g;
      }
      $root->{$key} = $value;
    }
  }
}

# -------------------------------------------------------------------
sub loadconfiguration {
  my $arg = shift;

  my @possibilities = (
		       $arg,
		       catfile( '/home', $ENV{'LOGNAME'}, ".${APP_NAME}.conf" ),
		       catfile( $FindBin::RealBin, "${APP_NAME}.conf" ),
		       catfile( $FindBin::RealBin, 'etc', "${APP_NAME}.conf"),
		       "$FindBin::RealBin/../etc/${APP_NAME}.conf"
		      );

  my $file;
  for my $f ( @possibilities ) { 
    if ( -e $f && -r _ ) {
      $file = $f;
      last;
    }
  }

  if ( !$file ) {
    confess "error - could not find the configuration file [$file]";
  }

  $OPT{configfile} = $file;

  my $conf = Config::General->new(
				  -ConfigFile        => $file,
				  -AllowMultiOptions => 1,
				  -LowerCaseNames    => 1,
				  -ConfigPath        => [
							 "$FindBin::RealBin/etc", "$FindBin::RealBin/../etc",
							 "$FindBin::RealBin/..",  $FindBin::RealBin,
							 dirname($file),          "$FindBin::RealBin/../" . dirname($file)
							],
				  -AutoTrue => 1
				 );

  %CONF = $conf->getall;
}

# -------------------------------------------------------------------
sub printsvg {
  print SVG @_, "\n" if $SVG_MAKE;
}

# -------------------------------------------------------------------
sub printdebug {
  printinfo( 'debug', @_ ) if $CONF{debug};
}

# -------------------------------------------------------------------
sub printdumper {
  $Data::Dumper::Sortkeys=1;
  $Data::Dumper::Indent=1;
  printinfo( Dumper(@_) );
}

# -------------------------------------------------------------------
sub printwarning {
  printinfo( 'warning', @_ ) if $CONF{warnings};
}

# -------------------------------------------------------------------
sub printinfo {
  printout( join( $SPACE, @_ ) );
}

# -------------------------------------------------------------------
sub printout {
  print "@_\n" unless $CONF{silent};
}

# -------------------------------------------------------------------

=pod

=head1 AUTHOR

Martin Krzywinski E<lt>martink at bcgsc.caE<gt>.

=head1 CITING

If you are using Circos in a publication, please cite as

Krzywinski, M., J. Schein, I. Birol, J. Connors, R. Gascoyne, D. Horsman, S. Jones, and M. Marra. 2009. Circos: an Information Aesthetic for Comparative Genomics. Genome Res (in press).

=head1 CONTRIBUTORS

Ken Youens-Clark E<lt>kyclark@gmail.comE<gt>

=head1 BUGS

Please report any bugs or feature requests to C<bug-circos at
rt.cpan.org>, or through the web interface at
L<http://rt.cpan.org/NoAuth/ReportBug.html?Queue=Circos>. I will be
notified, and then you'll automatically be notified of progress on
your bug as I make changes.

=head1 SUPPORT

You can find documentation for this module with the perldoc command.

    perldoc Circos

You can also look for information at:

=over 4

=item * Google Code project homepage

L<http://code.google.com/p/circos/>

=item * RT: CPAN's request tracker

L<http://rt.cpan.org/NoAuth/Bugs.html?Dist=Circos>

=item * AnnoCPAN: Annotated CPAN documentation

L<http://annocpan.org/dist/Circos>

=item * CPAN Ratings

L<http://cpanratings.perl.org/d/Circos>

=item * Search CPAN

L<http://search.cpan.org/dist/Circos/>

=back

=head1 ACKNOWLEDGEMENTS

=head1 SEE ALSO

=over

=item * online Circos table viewer

http://mkweb.bcgsc.ca/circos/tableviewer

Uses Circos to generate visualizations of tabular data.

=item * chromowheel

  Ekdahl, S. and E.L. Sonnhammer, ChromoWheel: a new spin on eukaryotic 
    chromosome visualization. Bioinformatics, 2004. 20(4): p. 576-7.

The ChromeWheel is a processing method for generating interactive
illustrations of genome data. With the process chromosomes, genes and
relations between these genes is displayed. The chromosomes are placed
in a circle to avoid lines representing relations crossing genes and
chromosomes.

http://chromowheel.cgb.ki.se/

=item * genopix

GenomePixelizer was designed to help in visualizing the relationships
between duplicated genes in genome(s) and to follow relationships
between members of gene clusters. GenomePixelizer may be useful in the
detection of duplication events in genomes, tracking the "footprints"
of evolution, as well as displaying the genetic maps and other aspects
of comparative genetics.

http://genopix.sourceforget.net

=back

=head1 COPYRIGHT & LICENSE

Copyright 2004-2009 Martin Krzywinski, all rights reserved.

This file is part of the Genome Sciences Centre Perl code base.

This script is free software; you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation; either version 2 of the License, or
(at your option) any later version.

This script is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with this script; if not, write to the Free Software Foundation,
Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA

=cut

1;
