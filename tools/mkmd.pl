#! /usr/bin/perl
# $Id:$

my $filename = $ARGV[0];

if ($filename =~ /\.v$/) {
    $lang = "coq";
} elsif ($filename =~ /\.swi$/) {
    $lang = "prolog";
} elsif ($filename =~ /\.[ch]$/) {
    $lang = "C";
}

my $debug = 0;

my $istext = 0;                             # Markdownの地のテキストである。
my $lastistext = 0;

my $isprog = 0;                             # Markdownのプログラム引用である。
my $lastisprog = 0;

while (<>) {
    chop;

    # プログラムの部分かどうかを判定する。
    if (/^\s*$/) {
        printf("\n");
        next;
    } elsif (/^\(\* END \*\)/i || /^\/\* END \*\//i) {
        next;
    } elsif (/^\(\*\* \s* $ /x || /^\/\*\* \s* $ /x) {
        $isprog = 0;
        next;
    } elsif ($isprog == 0 && (/^\s*\*\)/ || /^\s*\*\//)) {
        $isprog = 1;
        printf("\n");
        next;
    }

    # テキストの部分かどうかを判定する。
    # Markdownの指示記号から始まる行は、テキストに含めない。
    if ($isprog == 0 && /^\S/ && /^[^0-9#%=@\*\+\-\>\`]/) {
        $istext = 1;
    } else {
        $istext = 0;
    }
        
    # プログラムの部分を```でくくる。
   if ($lastisprog == 0 && $isprog == 1) {       # 開始か？
       printf("\n\n```%s:\n", $lang);            # ```開く。
    } elsif ($lastisprog == 1 && $isprog == 0) { # 終了か？
        printf("\n\n```\n");                     # ```閉じる。
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
