// Standalone Magma replay of the expanded review's calculation for n = 26.
SetSeed(20261105);
Z := Integers();
D := 104006;
E := EllipticCurve([-D^2, 0]);

G, map, rank_proven, saturation_proven := MordellWeilGroup(E : Effort := 1);
assert rank_proven and saturation_proven;
basis := [map(G.i) : i in [1 .. Ngens(G)] | Order(G.i) eq 0];
points := IntegralPoints(E : FBasis := basis);

coordinates := { <Z!P[1], Abs(Z!P[2])> : P in points };
assert coordinates eq {
    <-104006, 0>, <-102850, 4959240>, <-51842, 20529432>, <-49419, 20344155>,
    <-322, 1866312>, <-38, 641136>, <0, 0>, <104006, 0>, <104652, 3755844>,
    <208658, 82628568>, <18610956, 80287186980>, <33593938, 194710464648>,
    <284664422, 4802858127984>
};

solutions := Sort(Setseq({
    P[1] div D + 1 : P in coordinates | P[1] mod D eq 0 and P[1] div D + 1 gt 29
}));
assert solutions eq [324, 2738];
print "Mordell-Weil invariants", Invariants(G);
print "Rank and saturation proved", rank_proven, saturation_proven;
print "Integral points up to sign", #coordinates;
print "Factorial solutions for a3 = 26", solutions;
quit;
