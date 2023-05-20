#! /usr/bin/perl

my @list = `opam list`;

$ocaml = "none";
$coq = "none";
$mathcomp = "none";
$alg_tac = "none";
$elpi = "none";
$coq_elpi = "none";
$hb = "none";

foreach $pkg (@list)
{
    if ($pkg =~ /^ocaml\s+(\S+)\s/)
    {
        $ocaml = $1;
    }
    elsif ($pkg =~ /^coq\s+(\S+)\s/)
    {
        $coq = $1;
    }
    elsif ($pkg =~ /^coq-mathcomp-ssreflect\s+(\S+)\s/)
    {
        $mathcomp = $1;
    }
    elsif ($pkg =~ /^coq-mathcomp-algebra-tactics\s+(\S+)\s/)
    {
        $alg_tac = $1;
    }
    elsif ($pkg =~ /^elpi\s+(\S+)\s/)
    {
        $elpi = $1;
    }
    elsif ($pkg =~ /^coq-elpi\s+(\S+)\s/)
    {
        $coq_elpi = $1;
    }
    elsif ($pkg =~ /^coq-hierarchy-builder\s+(\S+)\s/)
    {
        $hb = $1;
    }
}

print "Coq:$coq, MathComp:$mathcomp\n";
print "OCaml:$ocaml, Coq:$coq, MathComp:$mathcomp, Algebra Tactics:$alg_tac, ELPI:$elpi, HB:$hb\n";

# END
