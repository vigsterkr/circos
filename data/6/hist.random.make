#!/home/martink/bin/perl

use strict;
use Math::VecStat qw(min max);
open(F,"/home/martink/work/ucsc/hg18/chrlengths.txt");
my $cl;
while(<F>) {
    chomp;
    next if /random/;
    my ($chr,$len) = split;
    $chr =~ s/chr//;
    $cl->{$chr} = $len;
}
close(F);

for my $chr (keys %$cl) {
  my $pos = 0;
  while($pos < $cl->{$chr}) {
    my $bin = max(2e6,rand(2e7));
    printf("hs%d %d %d %f\n",$chr,$pos,$pos+$bin,1-(2*rand()));
    $pos += $bin + 1 + rand(1e7);
  }
}
