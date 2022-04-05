require import AllCore.
require import Li2_params.
require import IntDiv.

op mod_pm m d =
  let r = m %% d in
  if r < m %/ 2 then r else r - d.

op power2round r d =
  let r' = r %% Li2_q in
  let r0 = mod_pm r' (2 ^ d) in
  ((r' - r0) %/ (2 ^ d), r0).

op decompose r alpha =
  let r' = r %% Li2_q in
  let r0 = mod_pm r' alpha in
  if (r - r0 = Li2_q - 1)
  then
    (0, r0 - 1)
  else
    ((r' - r0) %/ alpha, r0).

op highbits r alpha = (decompose r alpha).`1.

op lowbits r alpha = (decompose r alpha).`2.

op makeHint z r alpha =
  let r1 = highbits r alpha in
  let v1 = highbits (r + z) alpha in
  b2i (!(r1 = v1)).

op useHint h r alpha =
  let m = (Li2_q - 1) %/ alpha in
  let (r1, r0) = decompose r alpha in
  if h = 1 && 0 < r0 then
    (r1 + 1) %% m
  else if h = 1 && r0 <= 0 then
    (r1 - 1) %% m
  else
    r1.
