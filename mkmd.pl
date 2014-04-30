#! /usr/bin/perl

my $inprog = 0;
my $lastinprog = 0;

while (<>) {
    chop;

    if (/^\s*$/) {
        printf("\n");
        next;
    } elsif (/^\(\* END \*\)/i) {
        next;
    } elsif (/^\(\*\* \s* $ /x) {
        $inprog = 0;
        next;
    } elsif ($isprog == 0 && /^\s*\*\)/) {
        $inprog = 1;
        next;
    }

    if ($lastinprog == 1 &&
        $inprog == 0) {
        printf("\n```\n");
    } elsif ($lastinprog == 0 &&
             $inprog == 1) {
        printf("\n```\n");
    }
    
    if (0) {
        printf("%d ", $inprog);
    }
    printf("%s\n", $_);
    
    $lastinprog = $inprog;
}

if ($inprog == 1) {
    printf("\n```\n");
}

# END
