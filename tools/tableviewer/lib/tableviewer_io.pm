
use strict;

sub prep_handle {
  my $file = shift;
  my $inputhandle;
  if($file) {
    die "No such file $file" unless -e $file;
    open(F,$file);
    $inputhandle = \*FILE;
  } else {
    printdebug("using STDIN");
    $inputhandle = \*STDIN;
  }
}

return 1;
