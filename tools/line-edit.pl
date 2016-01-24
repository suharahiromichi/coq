#! /usr/local/bin/perl

# ファイルにおいて、一致する1行とその前後の空行を削除する。
# 一致する行は、1箇所だけとする（繰り返し実行すればよい）。
# 末尾に空行がある場合、その一つ前とマッチしても、空行は削除しない。
# 全体で2行以上あるものとする。1行だけのファイルは対応しない。

# 使い方
#  ./line-edit.pl SUPRESS_ALL < test.txt| 
#

my $pat = shift;
    
my $debug = 1;

my $line1 = "top";
my $line2 = "top";
my $line3 = "top";

my $data1;
my $data2;
my $data3;

while (<>) {
    $line1 = $line2;
    $line2 = $line3;
    if ($_ =~ /^\s*$/) {
        $line3 = "nul";                     # 空行
    } elsif ($_ =~ /$pat/) {
        $line3 = "cmp";
    } else {
        $line3 = "oth";
    }
    
    $data1 = $data2;
    $data2 = $data3;
    $data3 = $_;

if ($debug) {    
    printf ("lines %s %s %s\n", $line1, $line2, $line3);
}
    if ($line2 eq "cmp") {
        if      ($line1 eq "top" && $line3 eq "nul") {
            ;
        } elsif ($line1 eq "top" && $line3 eq "oth") {
            print $data3;
        } elsif ($line1 eq "nul" && $line3 eq "nul") {
            print $data1;                   # NULLを出力する。
        } elsif ($data1 eq "nul" && $line3 eq "oth") {
            print $data3;
        } elsif ($line1 eq "oth" && $line3 eq "nul") {
            print $data1;
        } elsif ($line1 eq "oth" && $line3 eq "oth") {
            print $data1, $data3;
        }
        # 残り物の処理
        while (<>) {
            print $_;
        }
        exit 1;
    } else {
        print $data1;
    }
}

if ($debug) {
    printf ("------\n");
    printf ("lines %s %s %s\n", $line1, $line2, $line3);
}

# シフトしていない。
if ($line3 eq "cmp") {
    if      ($line2 eq "top") {
        ;
    } elsif ($line2 eq "nul") {
        print $data2;                       # NULLを出力する。
    } elsif ($line2 eq "oth") {
        print $data2;
    }
    exit 1;
} else {
    print $data2;
    print $data3;
    exit 0;
}

# END
