
eta10 = IdentityMatrix[10];
eta10[[1,1]] = -1;
eta3 = IdentityMatrix[3];
eta3[[1,1]] = -1;

frameWAdS3up = {1/2*Exp[-3*omega/4]*(d[t]-Cosh[rho]*d[v]), 1/2*Exp[omega/4]*d[rho], 1/2*Exp[omega/4]*Sinh[rho]*d[v]};
frameWS3 = {1/2*Exp[Q/4]*d[psi], 1/2*Exp[Q/4]*Sin[psi]*d[phi1], 1/2*Exp[-3*Q/4]*(d[phi2]-Cos[psi]*d[phi1])};
dsWAdS3up = Simplify[frameWAdS3up . eta3 . frameWAdS3up];
dsWS3 = Simplify[frameWS3 . frameWS3];
VolWAdS3up = Apply[Wedge, frameWAdS3up];
VolWS3 = Apply[Wedge, frameWS3];
A1 = Sqrt[1-Exp[2*omega]]*(d[t]-Cosh[rho]*d[v]);
A2 = d[phi2]-Cos[psi]*d[phi1];
w1 = Exp[-(omega+Q)/2]*Delta*d[y3] + p*Exp[omega]*d[y4];
w2 = Exp[(omega+Q)/2]*Delta*d[y3] + p*Exp[Q]*d[y4];
evalDilaton = {Phi->Log[phi0]};

TimeLikeBundle = {
		"coord"-> {t, rho, v, psi, phi1, phi2, y1, y2, y3, y4},
		"ds2" -> (Exp[Q/2]*dsWAdS3up + Exp[omega/2]*dsWS3 + Exp[Phi]*(d[y1]^2 + d[y2]^2 + d[y3]^2 + d[y4]^2))/. evalDilaton ,
		"Phi" -> Log[phi0],
		"F3" -> -2/phi0*Exp[(omega-Q)/2](Exp[omega/4]*VolWAdS3up + Exp[Q/4]*VolWS3) +  Exp[-(omega+Q)/4]*Sqrt[Sinh[Q-omega]/phi0/2]*d[A1] ⋀ d[y4],
		"B2" -> -p/4*A1 ⋀ A2 - Exp[(omega+Q)/4]*Sqrt[phi0*(Sinh[Q-omega])/2]*A2 ⋀ w1,
		"F1" -> 0,
		"G5" -> 1/4*Exp[-omega/2-Q/2]*Delta*d[A1 ⋀ A2] ⋀ d[y1] ⋀ d[y2] - Exp[-5*Q/4]*Sqrt[2*Sinh[Q-omega]/phi0]*A2 ⋀ VolWAdS3up ⋀ w2,
		"assum" -> {u>0, 0<p<Exp[-(Q+omega)/2], phi0>0, Q>0, omega>Q, 0<theta<Pi/2, 0<psi<Pi/2},

		"e10" -> Flatten[{Exp[Q/4]*frameWAdS3up, Exp[omega/4]*frameWS3, Exp[Phi/2]*{d[y1], d[y2], d[y3], d[y4]}}] /. evalDilaton,
		"constants"-> {p,omega, Q, phi0, Delta},
		"assum"-> {rho>0, 0<p<Exp[-(Q+omega)/2], phi0>0, omega<0, Q>omega, 0<theta<Pi/2, 0<psi<Pi/2},
		"evals"-> <|"Delta"->{Delta -> Sqrt[1 - Exp[Q+omega]*p^2]}|>,
		"\[Eta]dd" -> eta10};

TimeLikeBundle = Association[TimeLikeBundle];
