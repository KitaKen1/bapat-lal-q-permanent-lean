import Lean

/-!
# Exact arithmetic for the ordered Bapat–Lal certificate

The arithmetic is checked by Lean's kernel. This module does not yet identify
its coefficient recurrence with the permutation definition of the q-permanent.
Source: ../01_Bapat元予想の反例_144次/展開済み/bapat_lal_certificate.json
-/

namespace Bapat.Certificate

abbrev Gaussian := Int × Int

def zero : Gaussian := (0, 0)
def add (x y : Gaussian) : Gaussian := (x.1 + y.1, x.2 + y.2)
def mul (x y : Gaussian) : Gaussian :=
  (x.1 * y.1 - x.2 * y.2, x.1 * y.2 + x.2 * y.1)
def scale (c : Int) (x : Gaussian) : Gaussian := (c * x.1, c * x.2)
def normSq (x : Gaussian) : Int := x.1 * x.1 + x.2 * x.2

def rows : List (Int × Int × Int) :=
  [(-60, 72, -35),
    (-55, 80, -21),
    (52, -85, -1),
    (49, -84, 21),
    (63, -61, 48),
    (52, -68, 52),
    (68, -51, 53),
    (39, -83, 40),
    (-41, 91, 5),
    (45, -58, 68),
    (59, -46, 66),
    (30, -95, 7),
    (32, -60, 73),
    (48, -83, -27),
    (49, -32, 81),
    (-21, 79, -57),
    (-44, 80, 41),
    (63, -29, 72),
    (36, -19, 91),
    (21, -23, 95),
    (14, -99, -4),
    (-33, 80, 51),
    (-73, 36, -59),
    (-48, 1, -88),
    (-19, 75, 64),
    (31, 21, 93),
    (59, -6, 80),
    (2, 93, -37),
    (5, 84, -55),
    (16, 70, 70),
    (45, 28, 85),
    (-24, -75, -61),
    (27, -43, -86),
    (34, 65, 68),
    (70, -7, 72),
    (-61, -18, -77),
    (45, 60, 67),
    (54, 42, 73),
    (20, 47, -86),
    (28, 96, 6),
    (76, -20, 62),
    (25, 86, -44),
    (28, 10, -96),
    (41, -51, -76),
    (44, 82, 37),
    (71, 16, 68),
    (66, 39, 64),
    (42, 91, 6),
    (61, 58, 54),
    (57, 72, 40),
    (42, 88, -22),
    (-53, -83, -15),
    (38, 59, -71),
    (42, 76, -50),
    (40, -7, -91),
    (41, 34, -84),
    (79, 5, 61),
    (77, 29, 57),
    (74, 46, 49),
    (68, 65, 33),
    (-55, -79, 27),
    (65, 75, 12),
    (61, 79, -11),
    (52, -56, -64),
    (50, -29, -82),
    (-55, -65, 53),
    (77, 54, 33),
    (-51, -4, 86),
    (75, 65, 15),
    (-54, -38, 75),
    (84, -11, 54),
    (71, 69, -10),
    (61, 49, -62),
    (66, 63, -41),
    (84, 37, 40),
    (86, 18, 48),
    (-72, -62, 31),
    (60, 14, -79),
    (81, 59, -3),
    (84, 53, 13),
    (79, 57, -20),
    (88, 41, 25),
    (90, 26, 36),
    (73, 45, -51),
    (69, 30, -66),
    (89, 4, 46),
    (91, 39, 13),
    (89, 45, -2),
    (61, -22, -76),
    (82, 42, -39),
    (86, 43, -27),
    (90, 41, -15),
    (71, 9, -70),
    (80, 29, -53),
    (95, 24, 20),
    (94, 12, 31),
    (69, -10, -71),
    (95, 30, -1),
    (78, 7, -62),
    (84, 17, -51),
    (90, 26, -36),
    (95, 27, -18),
    (92, -7, 38),
    (98, 19, 6),
    (66, -37, -65),
    (94, 16, -29),
    (98, 17, -12),
    (90, 8, -42),
    (99, 7, 14),
    (97, -1, 25),
    (-77, 20, 61),
    (100, 6, -1),
    (-85, 6, 52),
    (87, -27, 41),
    (66, -54, -53),
    (92, -19, 33),
    (99, 1, -15),
    (96, -2, -28),
    (92, -9, -39),
    (84, -22, -49),
    (-98, 12, -14),
    (76, -39, -52),
    (99, -12, 3),
    (99, -13, -9),
    (96, -17, -24),
    (95, -23, 20),
    (91, -27, -33),
    (85, -36, -39),
    (95, -27, -16),
    (69, -61, -39),
    (96, -28, -2),
    (86, -40, 32),
    (78, -51, -36),
    (94, -34, 8),
    (90, -39, 22),
    (89, -42, -17),
    (83, -52, -22),
    (88, -47, -7),
    (-73, 64, 24),
    (87, -49, 7),
    (84, -50, 22),
    (76, -63, -12),
    (82, -57, 10),
    (79, -62, -1)]

/-- Multiply an ascending coefficient list by `a + b*z`. -/
def mulLinear (a : Int) (b : Gaussian) (p : List Gaussian) : List Gaussian :=
  List.zipWith add ((p.map (scale a)) ++ [zero]) (zero :: p.map (mul b))

/-- Product and weighted endpoint polynomial, using the final-order weights. -/
def coefficientStep (n : Nat) (state : List Gaussian × List Gaussian)
    (row : (Int × Int × Int) × Nat) : List Gaussian × List Gaussian :=
  let a := row.1.1
  let b := (row.1.2.1, row.1.2.2)
  let weight : Int := (n : Int) - 1 - 2 * (row.2 : Int)
  (mulLinear a b state.1,
    List.zipWith add (mulLinear a b state.2)
      (state.1.map (mul (scale weight b))))

def coefficients : List Gaussian × List Gaussian :=
  rows.zipIdx.foldl (coefficientStep 144) ([(1, 0)], [])

def factorial : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * factorial n

def coefficientNorm (degree : Nat) (p : List Gaussian) : Int :=
  (p.zipIdx.map fun ck =>
    ((factorial ck.2 * factorial (degree - ck.2) : Nat) : Int) * normSq ck.1).sum

def computedP : Int := coefficientNorm 144 coefficients.1

def computedS : Int := coefficientNorm 142 (coefficients.2.take 143)

def expectedP : Int := 133678240032012707743341823506761537111390070639378925921169528089493990441983374531942708065983919533849579416400504077876793432116093328138905769259876664891009240873430688961941951637993850318470633426580331039188349271336664817712560264323794511627824625833122047978762887898638010693864123094257070180998235154110234932640934563961259441310792539159453396757009137044909821370675479701107755742220764878298101833517779237722959000105604189250200448302419674561581821654043644151351122051952949543947182998796533111193458306154652760192241178619186506682910315285966684165646978481181039816542461951152335689626359995521995625624680935134338831598816624625729320972871814954626056447910155529524648209418846471633548345344000000000000000000000000000000000000000000

def expectedS : Int := 1376947256712251988527177698496421832783993365319876688843607345214548644835359944258487135623099644280281994129571487988240187994619406497865166087623053161657377351239037033096522643562031212654113814860095789066933092894792871737810219567423916656760932098883132633868105690222267587879209667852183008903066040388799231855653865963226145264141678808440493760289983191817671140724919486663107265919625557046954084984389677468396424914424625055448542235362937766758637873717739832144148886628426721505768508549427863102833251095175279986416390403168726456754617783914880346446696648533341458622044716572868997966072028696973231703981212797812886373796055407211045988947836422702490210308411600335612148472652136936537814288302080000000000000000000000000000000000000000000

def gap : Int := expectedS - 10296 * expectedP

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The coefficient calculation reproduces both stored exact integers. -/
theorem exact_coefficients : computedP = expectedP ∧ computedS = expectedS := by
  decide +kernel

/-- The strict sign margin is an ordinary integer inequality. -/
theorem strict_margin : expectedS > 10300 * expectedP := by
  decide +kernel

/-- The integer certificate has strictly negative endpoint numerator. -/
theorem endpoint_numerator_negative : 10296 * expectedP - expectedS < 0 := by
  decide +kernel

/-- All 144 ordered rows are present. -/
theorem rows_length : rows.length = 144 := by
  decide +kernel

#print axioms exact_coefficients
#print axioms strict_margin
#print axioms endpoint_numerator_negative

end Bapat.Certificate
