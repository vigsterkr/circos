use strict;
use warnings;
use Module::Build;

my $builder = Module::Build->new(
    module_name         => 'Circos',
    license             => 'gpl',
    dist_author         => 'Martin Krzywinski <martink@bcgsc.ca>',
    dist_abstract       => 'Circular data visualizations',
    dist_version_from   => 'lib/Circos.pm',
    script_files        => ['bin/circos', 'bin/gddiag'],
    create_readme       => 0,
    requires => {
        'Class::Base'             => 0,
        'Config::General'         => 0,
        'Devel::DProf'            => 0,
        'GD::Polyline'            => 0,
        'GD'                      => 0,
        'Graphics::ColorObject'   => 0,
        'IO::Dir'                 => 0,
        'IO::File'                => 0,
        'List::MoreUtils'         => 0,
        'List::Util'              => 0,
        'Math::Bezier'            => 0,
        'Math::BigFloat'          => 0,
        'Math::Random'            => 0,
        'Math::Round'             => 0,
        'Math::VecStat'           => 0,
        'Memoize'                 => 0,
        'Params::Validate'        => 0,
        'Pod::Usage'              => 0,
        'Set::IntSpan'            => 0,
        'Statistics::Descriptive' => 0,
        'Storable'                => 0,
        'Time::HiRes'             => 0,
    },
    build_requires => {
        'Test::More' => 0,
    },
    add_to_cleanup      => [ 'Circos-*' ],
    create_makefile_pl => 'traditional',
);

$builder->create_build_script();
