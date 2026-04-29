eta10 = IdentityMatrix[10];
eta10[[1,1]] = -1;
eta3 = IdentityMatrix[3];
eta3[[1,1]] = -1;

frameWAdS3right = {Exp[omega/4]/2*d[t]*Sinh[rho], Exp[omega/4]/2*d[rho], Exp[-3*omega/4]/2*(d[theta]-Cosh[rho]*d[t])};
frameWS3 = {1/2*Exp[Q/4]*d[psi], 1/2*Exp[Q/4]*Sin[psi]*d[phi1], 1/2*Exp[-3*Q/4]*(d[phi2]-Cos[psi]*d[phi1])};
dsWAdS3right = Simplify[frameWAdS3right . eta3 . frameWAdS3right];
dsWS3 = Simplify[frameWS3 . frameWS3];
VolWAdS3right = Apply[Wedge, frameWAdS3right];
VolWS3 = Apply[Wedge, frameWS3];
A1 = d[theta]-Cosh[rho]*d[t];
A2 = Sqrt[Exp[2*Q]-1]*(d[phi2]-Cos[psi]*d[phi1]);
w1 = Exp[-(omega+Q)/2]*Delta*d[y3] - p*Exp[Q]*d[y4];
w2 = Exp[(omega+Q)/2]*Delta*d[y3] - p*Exp[omega]*d[y4];
evalDilaton = {Phi->Log[phi0]};

SpaceLikeBundle = {
		"coord"->{t, rho, theta, psi, phi1, phi2, y1, y2, y3, y4},
		"ds2" -> (Exp[Q/2]*dsWAdS3right + Exp[omega/2]*dsWS3 + Exp[Phi]*(d[y1]^2 + d[y2]^2 + d[y3]^2 + d[y4]^2)) /. evalDilaton,
		"Phi" -> Log[phi0],
		"F3" -> 2/phi0*Exp[(Q-omega)/2](Exp[omega/4]*VolWAdS3right + Exp[Q/4]*VolWS3) - Exp[-(omega+Q)/4]*Sqrt[Sinh[omega-Q]/phi0/2]*d[A2] ⋀ d[y4],
		"B2" -> -p/4*A1 ⋀ A2 - Exp[(omega+Q)/4]*Sqrt[phi0*Sinh[omega-Q]/2]*A1 ⋀ w1,
		"F1" -> 0,
		"G5" -> 1/4*Exp[-(omega + Q)/2]*Delta*d[A1 ⋀ A2] ⋀ d[y1] ⋀ d[y2] + Exp[-5*omega/4]*Sqrt[2*Sinh[omega-Q]/phi0]*A1 ⋀ VolWS3 ⋀ w2,
		"assum" -> {u>0, 0<p<Exp[-(Q+omega)/2], phi0>0, Q>0, omega>Q, 0<theta<Pi/2, 0<psi<Pi/2},
		"e10" -> Flatten[{Exp[Q/4]*frameWAdS3right, Exp[omega/4]*frameWS3, Exp[Phi/2]*{d[y1], d[y2], d[y3], d[y4]}} /. evalDilaton ],
		"constants"->{p,omega, Q, phi0, Delta},
		"assum"->{rho>0, 0<p<Exp[-(Q+omega)/2], phi0>0, Q>0, omega>Q, 0<theta<Pi/2, 0<psi<Pi/2},
		"evals"-><|"Delta"->{Delta -> Sqrt[1 - Exp[Q+omega]*p^2]}|>,
		"\[Eta]dd" -> eta10};

SpaceLikeBundle = Association[SpaceLikeBundle];

