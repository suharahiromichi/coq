#! /usr/bin/perl
# $Id:$

my $debug = 0;

my $istext = 0;
my $lastistext = 0;

my $isprog = 0;
my $lastisprog = 0;

while (<>) {
    chop;

    if (/^\s*$/) {
        printf("\n");
        next;
    } elsif (/^\(\* END \*\)/i) {
        next;
    } elsif (/^\(\*\* \s* $ /x) {
        $isprog = 0;
        next;
    } elsif ($isprog == 0 && /^\s*\*\)/) {
        $isprog = 1;
        next;
    }

    if ($isprog == 0 && /^\S/ && /^[^#=a-z0-9\*\+\>]/) {
        $istext = 1;
    } else {
        $istext = 0;
    }
    
    if ($lastisprog == 1 &&
        $isprog == 0) {
        printf("\n\n```\n");
    } elsif ($lastisprog == 0 &&
             $isprog == 1) {
        printf("\n\n```\n");
    }
    
    if ($debug == 1) {
        printf("\n");
        printf("%d %d ", $isprog, $istext);
    }

    if ($istext == 0) {
        printf("\n");
    }

    printf("%s", $_);
    
    $lastisprog = $isprog;
}

if ($isprog == 1) {
    printf("\n```\n");
}

# END
