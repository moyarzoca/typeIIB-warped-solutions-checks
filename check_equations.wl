CurrentDir  = DirectoryName[$InputFileName];
Get["/home/marcelo/repos/PaillacoDiff/PaillacoDiff.wl"];

Get[CurrentDir <> "typeIIBequations.wl"];

Print["========\n   LightLike\n======="];
Get[CurrentDir <> "lightlike/lightlike_configuration.wl"];
EqsLightLike = stringIIBequations[LightLikeBundle, LightLikeBundle["assum"], Simplify[#/.LightLikeBundle["evals","Delta"], LightLikeBundle["assum"]]&];
EqsLightLike = Simplify[EqsLightLike, LightLikeBundle["assum"]];
Export[CurrentDir <> "lightlike/equations.wl", EqsLightLike];
Print[EqsLightLike];

Print["========\n   SpaceLike\n======="];
Get[CurrentDir <> "spacelike/spacelike_configuration.wl"];
EqsSpaceLike = stringIIBequations[SpaceLikeBundle, SpaceLikeBundle["assum"], Simplify[#/.SpaceLikeBundle["evals","Delta"], SpaceLikeBundle["assum"]]&];
EqsSpaceLike = FullSimplify[EqsSpaceLike, SpaceLikeBundle["assum"]];
Export[CurrentDir <> "spacelike/equations.wl", EqsSpaceLike];
Print[EqsSpaceLike];

Print["========\n    TimeLike\n======="];
Get[CurrentDir <> "timelike/timelike_configuration.wl"];
EqsTimeLike = stringIIBequations[TimeLikeBundle, TimeLikeBundle["assum"], Simplify[#/.TimeLikeBundle["evals","Delta"], TimeLikeBundle["assum"]]&];
EqsTimeLike = Simplify[EqsTimeLike , TimeLikeBundle["assum"]];
Export[CurrentDir <> "timelike/equations.wl", EqsTimeLike];
Print[EqsTimeLike];
