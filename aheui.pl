#!/usr/bin/perl

=pod

=head1 NAME

aheui.pl - Perl interpreter for Aheui

=head1 DESCRIPTION

This is a pure Perl interpreter for the esoteric programming language Aheui.
More information about this language, including a semi-formal spec, 
can be found at the following locations:

	http://esolangs.org/wiki/Aheui
	
	https://github.com/aheui

This implementation is notable because it showcases many of the 
Unicode-related features of Perl.

=over

=item *

Literal Hangul characters as hash keys - no magic array indexes

=item *

Determining whether a character is a Hangul syllable by 
Unicode property - no hardcoded code points

=item *

Decomposing Hangul syllable to component letters by the 
Unicode::Normalize core module - no magic numbers and reimplemented algorithm

=back

=head1 USAGE

 [path/to/perl] aheui.pl [--debug] [--help] input.aheui

=head1 OPTIONS

	-l|--limit <n>	Limit number of instructions 
	-d|--debug		Print debug information after each instruction
	-h|--help		Print help and exit

=cut

use strict;
use warnings;
use 5.014;
use Unicode::Normalize 'decompose';
use utf8;
use integer;
#use Data::Dumper;
use Getopt::Long;
use Pod::Usage;

# STDIN and STDOUT in UTF-8
use open qw/:std :utf8/;

# flush STDOUT
$| = 1;

my $debug = 0;
my $help  = 0;
my $limit = undef;
GetOptions(
	'limit=i'  => \$limit,
	'debug!' => \$debug,
	'help!'  => \$help,
) or pod2usage(-verbose => 0);

pod2usage(-verbose => 1) if $help;

pod2usage(-verbose => 0) unless @ARGV;

# cursor position, program execution starts at top left
my ($cx, $cy) = (0, 0);

# current movement direction: down
my ($dx, $dy) = (0, 1);

# selected stack is the "empty trailing consonant" one
my $sp = "";

# program is running, i.e. not yet terminated
my $running = 1;

# number of instructions executed
my $ic = 0;

# vowel specifies direction of next move
my %dir = (
	ᅡ => sub { $dx =    1; $dy =    0 },
	ᅣ => sub { $dx =    2; $dy =    0 },
	ᅥ => sub { $dx =   -1; $dy =    0 },
	ᅧ => sub { $dx =   -2; $dy =    0 },
	ᅩ => sub { $dx =    0; $dy =   -1 },
	ᅭ => sub { $dx =    0; $dy =   -2 },
	ᅮ => sub { $dx =    0; $dy =    1 },
	ᅲ => sub { $dx =    0; $dy =    2 },
	ᅳ => sub { $dx =  $dx; $dy = -$dy },
	ᅴ => sub { $dx = -$dx; $dy = -$dy },
	ᅵ => sub { $dx = -$dx; $dy =  $dy },
);

# trailing consonant (cluster) can specify a literal integer 
my %literal = (
	"" => 0,
	ᆨ => 2,
	ᆩ => 4,
	ᆪ => 6,
	ᆫ => 2,
	ᆬ => 5,
	ᆭ => 5,
	ᆮ => 3,
	ᆯ => 5,
	ᆰ => 7,
	ᆱ => 9,
	ᆲ => 9,
	ᆳ => 7,
	ᆴ => 9,
	ᆵ => 9,
	ᆶ => 8,
	ᆷ => 4,
	ᆸ => 4,
	ᆹ => 6,
	ᆺ => 2,
	ᆻ => 4,
	ᆼ => 1,
	ᆽ => 3,
	ᆾ => 4,
	ᆿ => 3,
	ᇀ => 4,
	ᇁ => 4,
	ᇂ => 3,
#	ᇃ => 7,
);

# trailing consonants specifying IO
my $io_int = "ᆼ"; # as sp this selects the queue
my $io_uc  = "ᇂ";

# stacks as HoA's
my %stacks;
for (keys %literal) {
	$stacks{$_} = [];
}
my $storage = $stacks{$sp};
my $sp_is_queue = $sp eq $io_int;
my $sp_is_extension = $sp eq $io_uc;

# required number of elements on stack for given operation
my %req = (
	ᄀ => 0,
	ᄁ => 0,
	ᄂ => 2,
	ᄃ => 2,
	ᄄ => 2,
	ᄅ => 2,
	ᄆ => 1,
	ᄇ => 0,
	ᄈ => 1,
	ᄉ => 0,
	ᄊ => 1,
	ᄋ => 0,
	ᄌ => 2,
	ᄍ => 0,
	ᄎ => 1,
	ᄏ => 0,
	ᄐ => 2,
	ᄑ => 2,
	ᄒ => 0,
);


# leading consonants select command to execute
my %cmd = (
	ᄋ => sub { }, # nop
	ᄀ => sub { }, # spec doesn't mention these, implemented as nop
	ᄁ => sub { }, # nop?
	ᄍ => sub { }, # nop?
	ᄏ => sub { }, # nop?
	ᄃ => sub { my $x = popsp(); pushsp(popsp() + $x); },
	ᄐ => sub { my $x = popsp(); pushsp(popsp() - $x); },
	ᄄ => sub { my $x = popsp(); pushsp(popsp() * $x); },
	ᄂ => sub { my $x = popsp(); pushsp($x ? popsp() / $x : 0); },
	ᄅ => sub { my $x = popsp(); pushsp($x ? popsp() % $x : 0); },
	ᄆ => sub {
				if ($_[1]) {
					my $v = popsp();
					if ($_[0] eq $io_int) {
						print $v;
					}
					elsif ($_[0] eq $io_uc) {
						print chr $v;
					}
				}
				else {
					popsp();
				}
		 	  },
	ᄇ => sub {
				if ($_[1]) {
					my $v;
					if ($_[0] eq $io_int) {
						$v = <STDIN>;
						chomp $v;
					}
					elsif ($_[0] eq $io_uc) {
						$v = <STDIN>;
						chomp $v;
						$v = ord substr $v, 0, 1;
					}
					pushsp($v);
				}
				else {
					pushsp($literal{$_[0]});
				}
		 	  },
	ᄈ => sub {
				if ($sp_is_queue) {
					unshift @$storage, $storage->[0];
				}
				elsif ($sp_is_extension) {
					# do nothing
				}
				else {
					my $v = popsp();
					pushsp($v);
					pushsp($v);
				}
			  },
	ᄑ => sub {
				if ($sp_is_queue) {
					my $x = $storage->[0];
					$storage->[0] = $storage->[1];
					$storage->[1] = $x;
				}
				elsif ($sp_is_extension) {
					# do nothing
				}
				else {
					my $x = popsp();
					my $y = popsp();
					pushsp($x);
					pushsp($y);
				}
			  },
	ᄉ => sub {
				$sp = $_[0];
				$storage = $stacks{$sp};
				$sp_is_queue = $sp eq $io_int;
				$sp_is_extension = $sp eq $io_uc;
			  },
	ᄊ => sub {
				if ($sp_is_extension) {
					popsp(); # unimplemented extension 
				}
				else {
					push @{$stacks{$_[0]}}, popsp();
				}
			  },
	ᄌ => sub {
				my $x = popsp();
				my $y = popsp();
				pushsp($y >= $x ? 1 : 0);
			  },
	ᄎ => sub {
				if (popsp() == 0) {
					$dx = -$dx;
					$dy = -$dy;
				}
			  },

	ᄒ => sub { $running = 0; },
);

# read 2D Aheui code into AoA
open(my $FH, "<:encoding(UTF-8)", $ARGV[0]) or die "Can't open input file $ARGV[0]\n";
my @field;
my ($maxx, $maxy) = (0, 0);
while (<$FH>) {
	chomp;
	my @l = split //;
	$maxx = $maxx > @l ? $maxx : scalar @l;
	push @field, [ 
		map {
			my ($valid, $cmd, $dir, $arg, $is_io);
			# check if character is Hangul syllable
			if (/\p{Block: Hangul_Syllables}/) {
				# get character and decompose it
				($cmd, $dir, $arg) = split //, decompose($_);
				$valid = 1;
				$arg //= ""; #empty string if no trailing consonant/
				# dodgy optimization: check if arg is  
				# (meaning an IO operation for push/pull) and save it
				$is_io = ($arg eq $io_int or $arg eq $io_uc);
			}
			# cache components
			{valid => $valid, c => $_, cmd => $cmd, dir => $dir, arg => $arg, is_io => $is_io};
		} @l
	];
}
close $FH;

# pad lines with trailing whitespace
$maxy = scalar @field;
for (@field) {
	my $l = scalar @$_;
	push @$_, ({valid => 0, c => " "}) x ($maxx - $l);
}

# main loop, execute commands one by one, 
# moving between steps in the specified direction
while ($running) {
	my $c = $field[$cy][$cx];
	if ($c->{valid}) {
		my ($cmd, $dir, $arg) = ($c->{cmd}, $c->{dir}, $c->{arg});
		
		if ($debug) {
			print "\t$cx $cy [$c->{c}]";
			print " cmd[$cmd] dir[  $dir] arg[  $arg]" . 
				($c->{is_io} ? " IO" : "($literal{$arg})");
			print " sp[  $sp] ", join ",", @$storage;
			print "\n";
		}

		# set movement direction
		$dir{$dir}->() if exists $dir{$dir};
		
		# execute command
		if (@$storage >= $req{$cmd}) {
			$cmd{$cmd}->($arg, $c->{is_io});
		}
		else {
			# contrary to the spec, but similarly to reference JS implementation
			$dx = -$dx;
			$dy = -$dy;
		}
	}
	elsif ($debug) {
		print "\t$cx $cy [$c->{c}]";
		print "\n";
	}
	# move
	$cx += $dx;
	$cy += $dy;
	# wrap around
	$cx %= $maxx;
	$cy %= $maxy;
	
	# exit if over instruction limit
	$ic++;
	$running = 0 if defined $limit and $ic > $limit;
}

exit(popsp()) if scalar @$storage;


# utility functions to push/pop from/to selected stack
sub popsp {
	return 0 if $sp_is_extension;  # unimplemented extension
	return shift @$storage if $sp_is_queue; # queue
	pop @$storage; # stack
}

sub pushsp ($) {
	# extension unimplemented
	push @$storage, $_[0] unless $sp_is_extension;
}

