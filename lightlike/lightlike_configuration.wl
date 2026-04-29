
eta10 = IdentityMatrix[10];
eta10[[1,1]] = -1;
eta3 = IdentityMatrix[3];
eta3[[1,1]] = -1;
frameWAdS3zero = {d[xp] - (1 + 4*alpha)*d[xm]/4/u^2, d[u]/u, d[xp] + (1 - 4*alpha)*d[xm]/4/u^2};
frameWS3 = {1/2*Exp[Q/4]*d[psi], 1/2*Exp[Q/4]*Sin[psi]*d[phi1], 1/2*Exp[-3*Q/4]*(d[phi2]-Cos[psi]*d[phi1])};
dsWAdS3zero = Simplify[frameWAdS3zero.eta3.frameWAdS3zero];
dsWS3 = Simplify[frameWS3.frameWS3];
VolWAdS3zero = Apply[Wedge, frameWAdS3zero];
VolWS3 = Apply[Wedge, frameWS3];
A1 = d[xm]/u^2;
A2 = d[phi2] - Cos[psi]*d[phi1];
w = Exp[-Q]*Delta*d[y3] - p*d[y4];
evalDilaton = {Phi->Log[phi0]};

LightLikeBundle ={
	"coord"->{xp, u, xm, psi, phi1, phi2, y1, y2, y3, y4},
	"ds2" -> (dsWAdS3zero + Exp[-Q/2]*dsWS3 + Exp[Phi]*(d[y1]^2 + d[y2]^2 + d[y3]^2 + d[y4]^2)) /. evalDilaton,
	"Phi" -> Log[phi0],
	"F3" -> 2/phi0*(Exp[-Q]*VolWAdS3zero + Exp[-3*Q/4]*VolWS3) + Sqrt[alpha*(1 - Exp[-2*Q])/phi0]*d[A1] ⋀ d[y4],
	"B2" -> p/2*Sqrt[alpha]*A1 ⋀ A2 - 1/2*Sqrt[phi0*(Exp[2*Q]-1)]*A2 ⋀ w,
	"F1" -> 0,
	"G5" -> - Exp[-Q]*Sqrt[alpha]/2*Delta*d[A1 ⋀ A2] ⋀ d[y1] ⋀ d[y2] + Exp[-Q]*Sqrt[(Exp[2*Q]-1)/phi0]*A2 ⋀ VolWAdS3zero ⋀ w,
	"e10" -> Flatten[{frameWAdS3zero, Exp[-Q/4]*frameWS3, Exp[Phi/2]*{d[y1], d[y2], d[y3], d[y4]}}] /. evalDilaton,
	"constants"->{p,alpha, Q, phi0, Delta},
	"assum"->{u>0, 0<p<Exp[-Q], phi0>0, Q>0, 0<theta<Pi/2, 0<psi<Pi/2},
	"evals"-><|"Delta"->{Delta -> Sqrt[1 - Exp[2*Q]*p^2]}|>,
	"\[Eta]dd" -> eta10};

LightLikeBundle = Association[LightLikeBundle];
