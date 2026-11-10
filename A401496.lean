import Mathlib
/-!
# A401496 : matrices binaires de Riordan dont le complément est de Riordan

Preuve papier : Claude ; relecture, précisions et formalisation : ChatGPT,
2026-11-10.

Le compte `a` est défini par une image finie de matrices distinctes et un filtre
par leur complément ; la formule n'intervient pas dans sa définition.
La classification canonique est démontrée par appartenance, injectivité et
surjectivité, puis le cardinal est obtenu par `Finset.card_image_of_injective`.

Environnement : Lean 4.36.0-rc2, Mathlib
9d581dfff2e41de989072ea63abf3daf69311520.
-/
namespace A401496
open Finset
abbrev F₂ := ZMod 2
abbrev Jet (m : ℕ) := Fin m → F₂
abbrev Mat (m : ℕ) := Vector (Vector F₂ m) m

noncomputable def polynomial {m : ℕ} (g : Jet m) : Polynomial F₂ :=
  ∑ i : Fin m, Polynomial.monomial i.val (g i)

/-- Produit de séries tronquées calculable, convolution exacte. -/
def jetMul {m : ℕ} (g f : Jet m) : Jet m := fun i =>
  ∑ k : Fin (i.val + 1),
    g ⟨k.val, by omega⟩ * f ⟨i.val - k.val, by omega⟩

def jetOne (m : ℕ) : Jet m := fun i => if i.val = 0 then 1 else 0

def jetPow {m : ℕ} (f : Jet m) : ℕ → Jet m
  | 0 => jetOne m
  | j + 1 => jetMul (jetPow f j) f

def riordanMatrix {m : ℕ} (g f : Jet m) : Mat m :=
  Vector.ofFn fun i => Vector.ofFn fun j => jetMul g (jetPow f j.val) i

def full (m : ℕ) : Mat m :=
  Vector.ofFn fun i => Vector.ofFn fun j => if j.val ≤ i.val then 1 else 0

def complement {m : ℕ} (R : Mat m) : Mat m :=
  Vector.ofFn fun i => Vector.ofFn fun j => R[i][j] + (full m)[i][j]

def riordanMatrices (m : ℕ) : Finset (Mat m) :=
  ((Finset.univ : Finset (Jet m × Jet m)).filter
    (fun p => ∀ i : Fin m, i.val = 0 → p.2 i = 0)).image
    (fun p => riordanMatrix p.1 p.2)

def solutions (m : ℕ) : Finset (Mat m) :=
  let all := riordanMatrices m
  all.filter fun R => complement R ∈ all

/-- Nombre de graphes étiquetés, pas nombre de couples de paramètres. -/
def a (n : ℕ) : ℕ := if n = 0 then 0 else (solutions (n - 1)).card


abbrev Series := PowerSeries F₂
noncomputable def lift {m : ℕ} (g : Jet m) : Series :=
  PowerSeries.mk fun k => if h : k < m then g ⟨k, h⟩ else 0

noncomputable def jetOfSeries (m : ℕ) (s : Series) : Jet m :=
  fun i => PowerSeries.coeff i.val s

abbrev Congr (m : ℕ) (s t : Series) : Prop :=
  PowerSeries.trunc m s = PowerSeries.trunc m t

lemma congr_iff {m : ℕ} {s t : Series} :
    Congr m s t ↔ ∀ i < m, PowerSeries.coeff i s = PowerSeries.coeff i t := by
  constructor
  · intro h i hi
    have := congrArg (fun p : Polynomial F₂ => p.coeff i) h
    simpa [PowerSeries.coeff_trunc, hi] using this
  · intro h
    apply Polynomial.ext
    intro i
    by_cases hi : i < m
    · simpa [PowerSeries.coeff_trunc, hi] using h i hi
    · simp [PowerSeries.coeff_trunc, hi]

lemma congr_mul {m : ℕ} {s s' t t' : Series}
    (hs : Congr m s s') (ht : Congr m t t') : Congr m (s * t) (s' * t') := by
  have he := congrArg₂ (fun p q : Polynomial F₂ =>
    PowerSeries.trunc m ((p : Series) * (q : Series))) hs ht
  simpa only [PowerSeries.trunc_trunc_mul_trunc] using he

lemma congr_pow {m : ℕ} {s t : Series} (h : Congr m s t) (j : ℕ) :
    Congr m (s ^ j) (t ^ j) := by
  induction j with
  | zero => rfl
  | succ j ih => simpa only [pow_succ] using congr_mul ih h

lemma lift_of_series (m : ℕ) (s : Series) : Congr m (lift (jetOfSeries m s)) s := by
  apply congr_iff.mpr
  intro i hi
  simp [lift, jetOfSeries, PowerSeries.coeff_mk, hi]

lemma jetMul_coeff {m : ℕ} (g f : Jet m) (i : Fin m) :
    jetMul g f i = PowerSeries.coeff i.val (lift g * lift f) := by
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  unfold jetMul
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro k hk
  have hklt : k.val < m := by omega
  have hilt : i.val - k.val < m := by omega
  simp [lift, PowerSeries.coeff_mk, hklt, hilt]

lemma lift_mul {m : ℕ} (g f : Jet m) : Congr m (lift (jetMul g f)) (lift g * lift f) := by
  apply congr_iff.mpr
  intro i hi
  simpa [lift, PowerSeries.coeff_mk, hi] using jetMul_coeff g f ⟨i, hi⟩

lemma lift_one (m : ℕ) : Congr m (lift (jetOne m)) 1 := by
  apply congr_iff.mpr
  intro i hi
  simp [lift, jetOne, PowerSeries.coeff_mk, PowerSeries.coeff_one, hi]

lemma lift_pow {m : ℕ} (f : Jet m) (j : ℕ) : Congr m (lift (jetPow f j)) (lift f ^ j) := by
  induction j with
  | zero => exact lift_one m
  | succ j ih =>
    exact (lift_mul (jetPow f j) f).trans (by
      simpa only [pow_succ] using congr_mul ih (show Congr m (lift f) (lift f) from rfl))

lemma matrix_entry {m : ℕ} (g f : Jet m) (i j : Fin m) :
    (riordanMatrix g f)[i][j] = PowerSeries.coeff i.val (lift g * lift f ^ j.val) := by
  simp only [riordanMatrix, Fin.getElem_fin, Vector.getElem_ofFn]
  rw [jetMul_coeff]
  exact congr_iff.mp (congr_mul (show Congr m (lift g) (lift g) from rfl) (lift_pow f j.val))
    i.val i.isLt


lemma lift_const_zero {m : ℕ} (f : Jet m)
    (hf : ∀ i : Fin m, i.val = 0 → f i = 0) :
    PowerSeries.constantCoeff (lift f) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff]
  simp only [lift, PowerSeries.coeff_mk]
  split_ifs with hm
  · exact hf ⟨0, hm⟩ rfl
  · rfl

/-- Fidélité : l'image finie est exactement l'ensemble défini par des séries formelles. -/
theorem mem_riordan_iff {m : ℕ} (R : Mat m) :
    R ∈ riordanMatrices m ↔ ∃ g f : Series,
      PowerSeries.constantCoeff f = 0 ∧
      ∀ i j : Fin m, R[i][j] = PowerSeries.coeff i.val (g * f ^ j.val) := by
  constructor
  · intro h
    obtain ⟨⟨g, f⟩, hgf, rfl⟩ := Finset.mem_image.mp h
    have hf := (Finset.mem_filter.mp hgf).2
    exact ⟨lift g, lift f, lift_const_zero f hf, matrix_entry g f⟩
  · rintro ⟨g, f, hf, hR⟩
    apply Finset.mem_image.mpr
    refine ⟨(jetOfSeries m g, jetOfSeries m f), ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      intro i hi
      simpa [jetOfSeries, hi, PowerSeries.coeff_zero_eq_constantCoeff] using hf
    · apply Vector.ext
      intro i hi
      apply Vector.ext
      intro j hj
      change (riordanMatrix (jetOfSeries m g) (jetOfSeries m f))[(⟨i, hi⟩ : Fin m)][(⟨j, hj⟩ : Fin m)] =
        R[(⟨i, hi⟩ : Fin m)][(⟨j, hj⟩ : Fin m)]
      rw [matrix_entry, hR]
      exact congr_iff.mp (congr_mul (lift_of_series m g)
        (congr_pow (lift_of_series m f) j)) i hi

lemma complement_involutive {m : ℕ} (R : Mat m) :
    complement (complement R) = R := by
  apply Vector.ext
  intro i hi
  apply Vector.ext
  intro j hj
  simp only [complement, Vector.getElem_ofFn, Fin.getElem_fin]
  have hh : (full m)[i][j] + (full m)[i][j] = 0 := CharTwo.add_self_eq_zero _
  linear_combination hh

lemma mem_solutions {m : ℕ} (R : Mat m) :
    R ∈ solutions m ↔ R ∈ riordanMatrices m ∧ complement R ∈ riordanMatrices m := by
  simp [solutions]

lemma complement_mem_solutions {m : ℕ} (R : Mat m) :
    complement R ∈ solutions m ↔ R ∈ solutions m := by
  rw [mem_solutions, mem_solutions, complement_involutive]
  exact and_comm


def zeroMat (m : ℕ) : Mat m := Vector.replicate m (Vector.replicate m 0)

lemma mem_riordan_lower {m : ℕ} (R : Mat m) (hR : R ∈ riordanMatrices m)
    (i j : Fin m) (hij : i.val < j.val) : R[i][j] = 0 := by
  obtain ⟨g, f, hf, h⟩ := (mem_riordan_iff R).mp hR
  rw [h]
  have hdiv : (PowerSeries.X : Series) ^ j.val ∣ g * f ^ j.val :=
    dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd (PowerSeries.X_dvd_iff.mpr hf) j.val) g
  exact PowerSeries.X_pow_dvd_iff.mp hdiv i.val hij

lemma zero_mem_riordan (m : ℕ) : zeroMat m ∈ riordanMatrices m := by
  apply (mem_riordan_iff _).mpr
  refine ⟨0, 0, by simp, ?_⟩
  intro i j
  simp [zeroMat]

lemma full_mem_riordan (m : ℕ) : full m ∈ riordanMatrices m := by
  apply (mem_riordan_iff _).mpr
  refine ⟨PowerSeries.mk (fun _ => 1), PowerSeries.X, by simp, ?_⟩
  intro i j
  simp [full, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_mk]

lemma complement_zero (m : ℕ) : complement (zeroMat m) = full m := by
  apply Vector.ext
  intro i hi
  apply Vector.ext
  intro j hj
  simp [complement, zeroMat]

lemma zero_mem_solutions (m : ℕ) : zeroMat m ∈ solutions m := by
  rw [mem_solutions, complement_zero]
  exact ⟨zero_mem_riordan m, full_mem_riordan m⟩

lemma full_mem_solutions (m : ℕ) : full m ∈ solutions m := by
  rw [← complement_zero]
  exact (complement_mem_solutions _).mpr (zero_mem_solutions m)

/-- La première colonne nulle force la matrice Riordan à être nulle. -/
lemma zero_of_first_column {m : ℕ} (hm : 0 < m) (R : Mat m)
    (hR : R ∈ riordanMatrices m)
    (hfirst : ∀ i : Fin m, R[i][(⟨0, hm⟩ : Fin m)] = 0) : R = zeroMat m := by
  obtain ⟨g, f, hf, h⟩ := (mem_riordan_iff R).mp hR
  have hg : Congr m g 0 := by
    apply congr_iff.mpr
    intro i hi
    have h0 := hfirst ⟨i, hi⟩
    rw [h] at h0
    simpa using h0
  apply Vector.ext
  intro i hi
  apply Vector.ext
  intro j hj
  have hc := congr_iff.mp (congr_mul hg (show Congr m (f ^ j) (f ^ j) from rfl)) i hi
  calc R[i][j] = PowerSeries.coeff i (g * f ^ j) := h ⟨i, hi⟩ ⟨j, hj⟩
       _ = 0 := by simpa using hc
       _ = (zeroMat m)[i][j] := by simp [zeroMat]


lemma binary_cases (x : F₂) : x = 0 ∨ x = 1 := by
  fin_cases x
  · exact Or.inl rfl
  · exact Or.inr rfl

def topLeft {m : ℕ} (hm : 0 < m) (R : Mat m) : F₂ :=
  R[(⟨0, hm⟩ : Fin m)][(⟨0, hm⟩ : Fin m)]

lemma topLeft_complement {m : ℕ} (hm : 0 < m) (R : Mat m) :
    topLeft hm (complement R) = topLeft hm R + 1 := by
  simp [topLeft, complement, full]

lemma topLeft_complement_zero {m : ℕ} (hm : 0 < m) (R : Mat m) :
    topLeft hm (complement R) = 0 ↔ topLeft hm R ≠ 0 := by
  rw [topLeft_complement]
  rcases binary_cases (topLeft hm R) with h | h <;> rw [h] <;> norm_num [F₂]
  exact CharP.cast_eq_zero F₂ 2

/-- Première partie du comptage par involution, sans classification des paramètres. -/
theorem card_solutions_twice {m : ℕ} (hm : 0 < m) :
    (solutions m).card = 2 * ((solutions m).filter fun R => topLeft hm R = 0).card := by
  let Z := (solutions m).filter fun R => topLeft hm R = 0
  let O := (solutions m).filter fun R => topLeft hm R ≠ 0
  have hZO : ∀ R ∈ Z, complement R ∈ O := by
    intro R hR
    obtain ⟨hs, hz⟩ := Finset.mem_filter.mp hR
    apply Finset.mem_filter.mpr
    refine ⟨(complement_mem_solutions R).mpr hs, ?_⟩
    rw [topLeft_complement, hz]
    norm_num
  have hOZ : ∀ R ∈ O, complement R ∈ Z := by
    intro R hR
    obtain ⟨hs, ho⟩ := Finset.mem_filter.mp hR
    exact Finset.mem_filter.mpr ⟨(complement_mem_solutions R).mpr hs,
      (topLeft_complement_zero hm R).mpr ho⟩
  have hc : Z.card = O.card := Finset.card_bij'
    (fun R _ => complement R) (fun R _ => complement R) hZO hOZ
    (fun R _ => complement_involutive R) (fun R _ => complement_involutive R)
  have hs : Z.card + O.card = (solutions m).card :=
    Finset.card_filter_add_card_filter_not (s := solutions m) (p := fun R => topLeft hm R = 0)
  change (solutions m).card = 2 * Z.card
  omega


def positiveSolutions (m : ℕ) (hm : 0 < m) : Finset (Mat m) :=
  (solutions m).filter fun R => topLeft hm R = 0 ∧ R ≠ zeroMat m

theorem card_solutions_two_add_twice {m : ℕ} (hm : 0 < m) :
    (solutions m).card = 2 + 2 * (positiveSolutions m hm).card := by
  let Z := (solutions m).filter fun R => topLeft hm R = 0
  have hz : zeroMat m ∈ Z := by
    apply Finset.mem_filter.mpr
    refine ⟨zero_mem_solutions m, ?_⟩
    simp [topLeft, zeroMat]
  have he : Z.erase (zeroMat m) = positiveSolutions m hm := by
    ext R
    simp only [Z, positiveSolutions, Finset.mem_erase, Finset.mem_filter]
    tauto
  have hc := Finset.card_erase_add_one hz
  rw [he] at hc
  have hs := card_solutions_twice hm
  change (solutions m).card = 2 * Z.card at hs
  omega

#print axioms card_solutions_two_add_twice
#print axioms card_solutions_twice
#print axioms mem_riordan_iff
#print axioms zero_of_first_column
end A401496

namespace RiordanCore
variable {A : Type*} [CommRing A]

/-- Deux premières identités de colonnes impliquent l'obstruction quadratique. -/
theorem obstruction {G H f t k : A} (hH : H = 1 + G)
    (h1 : H * k = G * f + t) (h2 : H * k ^ 2 = G * f ^ 2 + t ^ 2) :
    G * (f - t) ^ 2 = 0 := by
  have he : (G * f + t) ^ 2 = H * (G * f ^ 2 + t ^ 2) := by
    rw [← h1, ← h2]
    ring
  rw [hH] at he
  linear_combination -he

/-- La même obstruction est suffisante pour toutes les puissances, sans division
ni exposant négatif. Valable dans tout anneau commutatif, même avec nilpotents. -/
theorem all_columns {G H f t k : A} (hH : H = 1 + G) (hunit : IsUnit H)
    (h1 : H * k = G * f + t) (hobs : G * (f - t) ^ 2 = 0) :
    ∀ j : ℕ, H * k ^ j = G * f ^ j + t ^ j := by
  intro j
  induction j with
  | zero => simp [hH, add_comm]
  | succ j ih =>
    obtain ⟨z, hz⟩ := sub_dvd_pow_sub_pow f t j
    have hz0 : G * (f - t) * (f ^ j - t ^ j) = 0 := by
      calc G * (f - t) * (f ^ j - t ^ j) = (G * (f - t) ^ 2) * z := by
              rw [hz]; ring
           _ = 0 := by rw [hobs]; ring
    have he : (G * f + t) * (G * f ^ j + t ^ j) =
        H * (G * f ^ (j + 1) + t ^ (j + 1)) := by
      rw [hH]
      linear_combination -hz0
    apply hunit.mul_left_cancel
    calc H * (H * k ^ (j + 1)) = (H * k) * (H * k ^ j) := by ring
         _ = (G * f + t) * (G * f ^ j + t ^ j) := by rw [h1, ih]
         _ = H * (G * f ^ (j + 1) + t ^ (j + 1)) := he

theorem all_columns_iff {G H f t k : A} (hH : H = 1 + G) (hunit : IsUnit H)
    (h1 : H * k = G * f + t) :
    (∀ j : ℕ, H * k ^ j = G * f ^ j + t ^ j) ↔ G * (f - t) ^ 2 = 0 := by
  constructor
  · intro hc
    exact obstruction hH h1 (hc 2)
  · exact all_columns hH hunit h1

#print axioms all_columns_iff
end RiordanCore

namespace A401496
noncomputable def truncIdeal (m : ℕ) : Ideal Series :=
  Ideal.span {(PowerSeries.X : Series) ^ m}
abbrev Truncated (m : ℕ) := Series ⧸ truncIdeal m
noncomputable def quotientMap (m : ℕ) : Series →+* Truncated m :=
  Ideal.Quotient.mk (truncIdeal m)

lemma quotient_eq_iff {m : ℕ} (s t : Series) :
    quotientMap m s = quotientMap m t ↔ Congr m s t := by
  change Ideal.Quotient.mk (truncIdeal m) s = Ideal.Quotient.mk (truncIdeal m) t ↔ _
  rw [Ideal.Quotient.eq]
  change s - t ∈ Ideal.span {(PowerSeries.X : Series) ^ m} ↔ _
  rw [Ideal.mem_span_singleton, PowerSeries.X_pow_dvd_iff, congr_iff]
  simp only [map_sub, sub_eq_zero]

/-- L'obstacle dans les séries tronquées est nécessaire et suffisant pour toutes
les colonnes normalisées. Le cas m≤2 sera traité séparément lors du comptage. -/
theorem normalized_complement_criterion (m : ℕ) (hm : 3 ≤ m) (g f : Series)
    (hg : PowerSeries.constantCoeff g = 0) (hf : PowerSeries.constantCoeff f = 0) :
    let G := (1 + PowerSeries.X) * g
    let H := 1 + G
    (∃ k : Series, PowerSeries.constantCoeff k = 0 ∧
      ∀ j < m, Congr m (H * k ^ j) (G * f ^ j + PowerSeries.X ^ j)) ↔
      Congr m (G * (f - PowerSeries.X) ^ 2) 0 := by
  intro G H
  have hunit : IsUnit H := by
    apply PowerSeries.isUnit_iff_constantCoeff.mpr
    simp [H, G, hg]
  have hHq : quotientMap m H = 1 + quotientMap m G := by simp [H]
  constructor
  · rintro ⟨k, hk, hcols⟩
    have h1 := (quotient_eq_iff _ _).mpr (hcols 1 (by omega))
    have h2 := (quotient_eq_iff _ _).mpr (hcols 2 (by omega))
    simp only [map_mul, map_add, map_pow, pow_one] at h1 h2
    apply (quotient_eq_iff _ _).mp
    simpa only [map_mul, map_sub, map_pow, map_zero] using
      RiordanCore.obstruction hHq h1 h2
  · intro hobs
    obtain ⟨u, hu⟩ := hunit
    let k : Series := (↑(u⁻¹) : Series) * (G * f + PowerSeries.X)
    have h1 : H * k = G * f + PowerSeries.X := by
      calc H * k = ((u : Series) * (↑(u⁻¹) : Series)) * (G * f + PowerSeries.X) := by
              rw [hu]; ring
           _ = G * f + PowerSeries.X := by simp
    have hk : PowerSeries.constantCoeff k = 0 := by
      have hc := congrArg PowerSeries.constantCoeff h1
      simpa [H, G, hg, hf] using hc
    refine ⟨k, hk, ?_⟩
    have h1q := congrArg (quotientMap m) h1
    simp only [map_mul, map_add] at h1q
    have hobsq := (quotient_eq_iff _ _).mpr hobs
    simp only [map_mul, map_sub, map_pow, map_zero] at hobsq
    have hall := RiordanCore.all_columns hHq (IsUnit.map (quotientMap m) ⟨u, hu⟩) h1q hobsq
    intro j hj
    apply (quotient_eq_iff _ _).mp
    simpa only [H,G,map_one,map_mul, map_add, map_pow] using hall j

#print axioms normalized_complement_criterion
end A401496

namespace A401496
lemma congr_mono {m r : ℕ} (hr : r ≤ m) {s t : Series} (h : Congr m s t) :
    Congr r s t := congr_iff.mpr (fun i hi => congr_iff.mp h i (by omega))

lemma congr_add {m : ℕ} {s s' t t' : Series}
    (hs : Congr m s s') (ht : Congr m t t') : Congr m (s+t) (s'+t') := by
  exact congr_iff.mpr (fun i hi => by simp only [map_add]; rw [congr_iff.mp hs i hi, congr_iff.mp ht i hi])

lemma congr_shift {m v : ℕ} {s t : Series} :
    Congr m (PowerSeries.X^v*s) (PowerSeries.X^v*t) ↔ Congr (m-v) s t := by
  rw [congr_iff, congr_iff]
  constructor
  · intro h i hi
    have hh := h (i+v) (by omega)
    simpa using hh
  · intro h i hi
    simp only [PowerSeries.coeff_X_pow_mul']
    split_ifs with hv
    · exact h (i-v) (by omega)
    · rfl

lemma congr_cancel_unit {m : ℕ} {u s t : Series} (hu : IsUnit u) :
    Congr m (u*s) (u*t) ↔ Congr m s t := by
  constructor
  · intro h
    obtain ⟨a, rfl⟩ := hu
    have hc := congr_mul (show Congr m (↑(a⁻¹) : Series) ↑(a⁻¹) from rfl) h
    simpa only [← mul_assoc, Units.inv_mul, one_mul] using hc
  · intro h
    exact congr_mul rfl h

noncomputable def allOnes : Series := PowerSeries.mk fun _ => 1

lemma allOnes_inverse : (1 + PowerSeries.X) * allOnes = 1 := by
  ext i
  rw [add_mul, one_mul, mul_comm PowerSeries.X]
  have hX : (PowerSeries.X : Series) = PowerSeries.X ^ 1 := by simp
  rw [hX, map_add, PowerSeries.coeff_mul_X_pow']
  cases i with
  | zero => simp [allOnes, PowerSeries.coeff_mk, PowerSeries.coeff_one]
  | succ i => simp [allOnes, PowerSeries.coeff_mk, PowerSeries.coeff_one, CharTwo.add_self_eq_zero]

abbrev Represents {m : ℕ} (R : Mat m) (g f : Series) : Prop :=
  ∀ i j : Fin m, R[i][j] = PowerSeries.coeff i.val (g * f ^ j.val)

lemma complement_rep_iff {m : ℕ} {R : Mat m} {g f h k : Series}
    (hR : Represents R g f) :
    Represents (complement R) h k ↔
      ∀ j < m, Congr m (h*k^j) (g*f^j+allOnes*PowerSeries.X^j) := by
  constructor
  · intro hC j hj
    apply congr_iff.mpr
    intro i hi
    have hc := hC ⟨i,hi⟩ ⟨j,hj⟩
    simp only [complement, Fin.getElem_fin, Vector.getElem_ofFn] at hc
    have hr := hR ⟨i,hi⟩ ⟨j,hj⟩
    simp only [Fin.getElem_fin] at hr
    rw [hr] at hc
    simpa [map_add, allOnes, PowerSeries.coeff_mk, PowerSeries.coeff_mul_X_pow', full] using hc.symm
  · intro hC i j
    have hc := congr_iff.mp (hC j.val j.isLt) i.val i.isLt
    simp only [complement, Fin.getElem_fin, Vector.getElem_ofFn]
    have hr := hR i j
    simp only [Fin.getElem_fin] at hr
    rw [hr]
    simpa [map_add, allOnes, PowerSeries.coeff_mk, PowerSeries.coeff_mul_X_pow', full] using hc.symm

lemma complement_normalized_iff {m : ℕ} (hm : 0 < m) {R : Mat m} {g f : Series}
    (hR : Represents R g f) :
    complement R ∈ riordanMatrices m ↔
      ∃ k : Series, PowerSeries.constantCoeff k = 0 ∧
        ∀ j < m, Congr m ((1+(1+PowerSeries.X)*g)*k^j)
          (((1+PowerSeries.X)*g)*f^j+PowerSeries.X^j) := by
  let q := quotientMap m
  have hs : q (1+PowerSeries.X) * q allOnes = 1 := by
    rw [← map_mul, allOnes_inverse, map_one]
  constructor
  · intro hC
    obtain ⟨h,k,hk,hRep⟩ := (mem_riordan_iff _).mp hC
    have hc := (complement_rep_iff hR).mp hRep
    have h0 := (quotient_eq_iff _ _).mpr (hc 0 hm)
    simp only [pow_zero, mul_one, map_add] at h0
    refine ⟨k,hk,?_⟩
    intro j hj
    have hjq := (quotient_eq_iff _ _).mpr (hc j hj)
    simp only [map_add, map_mul, map_pow] at hjq
    apply (quotient_eq_iff _ _).mp
    change (1+q (1+PowerSeries.X)*q g)*q k^j =
      q (1+PowerSeries.X)*q g*q f^j+q PowerSeries.X^j
    change q h = q g + q allOnes at h0
    linear_combination q (1+PowerSeries.X)*hjq -
      q (1+PowerSeries.X)*q k^j*h0 - (q k^j-q PowerSeries.X^j)*hs
  · rintro ⟨k,hk,hc⟩
    apply (mem_riordan_iff _).mpr
    refine ⟨g+allOnes,k,hk,(complement_rep_iff hR).mpr ?_⟩
    intro j hj
    have hjq := (quotient_eq_iff _ _).mpr (hc j hj)
    simp only [map_add, map_mul, map_pow, map_one] at hjq
    change (1+q (1+PowerSeries.X)*q g)*q k^j =
      q (1+PowerSeries.X)*q g*q f^j+q PowerSeries.X^j at hjq
    apply (quotient_eq_iff _ _).mp
    change (q g+q allOnes)*q k^j = q g*q f^j+q allOnes*q PowerSeries.X^j
    linear_combination q allOnes*hjq +
      (q g*q f^j-q g*q k^j)*hs

#print axioms complement_normalized_iff

/-- Paramètres finis des matrices de valuation strictement positive. -/
abbrev PositiveCode (m : ℕ) :=
  (i : Fin (m - 1)) × (Jet i.val × Jet ((i.val + 1) / 2))

abbrev codeR {m : ℕ} (c : PositiveCode m) := c.1.val+1
abbrev codeV {m : ℕ} (c : PositiveCode m) := m-codeR c
abbrev codeCut {m : ℕ} (c : PositiveCode m) := codeR c-codeR c/2

def canonicalG {m : ℕ} (c : PositiveCode m) : Jet m := fun i =>
  if hlo : i.val < codeV c then 0 else
    if heq : i.val = codeV c then 1 else
      c.2.1 ⟨i.val-codeV c-1, by have hc := c.1.isLt; dsimp [codeV,codeR] at *; omega⟩

def canonicalF {m : ℕ} (c : PositiveCode m) : Jet m := fun i =>
  if hr : i.val < codeR c then
    if hs : i.val < codeCut c then (if i.val = 1 then 1 else 0)
    else c.2.2 ⟨i.val-codeCut c, by dsimp [codeCut,codeR] at *; omega⟩
  else 0

def canonicalMatrix (m : ℕ) (c : PositiveCode m) : Mat m :=
  riordanMatrix (canonicalG c) (canonicalF c)

noncomputable def canonicalU {m : ℕ} (c : PositiveCode m) : Series :=
  1+PowerSeries.X^1*lift c.2.1

lemma code_bounds {m : ℕ} (c : PositiveCode m) :
    0 < codeV c ∧ codeV c < m ∧ 0 < codeR c ∧ codeR c < m ∧
      codeV c+codeR c=m ∧ 0 < codeCut c := by
  have hc := c.1.isLt
  dsimp [codeV,codeR,codeCut]
  omega

lemma canonicalU_unit {m : ℕ} (c : PositiveCode m) : IsUnit (canonicalU c) := by
  apply PowerSeries.isUnit_iff_constantCoeff.mpr
  simp [canonicalU]

lemma canonicalG_factor {m : ℕ} (c : PositiveCode m) :
    Congr m (lift (canonicalG c)) (PowerSeries.X^(codeV c)*canonicalU c) := by
  apply congr_iff.mpr
  intro i hi
  have hb := code_bounds c
  have hc := c.1.isLt
  simp only [lift, PowerSeries.coeff_mk, dite_eq_left hi, PowerSeries.coeff_X_pow_mul',
    canonicalU, map_add, PowerSeries.coeff_one]
  by_cases hlo : i < codeV c
  · simp [canonicalG, hlo, show ¬codeV c ≤ i by omega]
  · have hle : codeV c ≤ i := by omega
    by_cases heq : i = codeV c
    · simp [canonicalG, heq]
    · have ht : i-codeV c-1 < c.1.val := by dsimp [codeV,codeR] at *; omega
      simp [canonicalG, hlo, heq, hle, show i-codeV c ≠ 0 by omega,
        show 1 ≤ i-codeV c by omega, ht]

lemma canonical_first_column {m : ℕ} (c : PositiveCode m) (hm : 0 < m) (i : Fin m) :
    (canonicalMatrix m c)[i][(⟨0,hm⟩ : Fin m)] = canonicalG c i := by
  rw [canonicalMatrix, matrix_entry]
  simp [lift, PowerSeries.coeff_mk, i.isLt]

lemma canonicalG_constant {m : ℕ} (c : PositiveCode m) :
    PowerSeries.constantCoeff (lift (canonicalG c)) = 0 := by
  apply lift_const_zero
  intro i hi
  have hb := code_bounds c
  simp [canonicalG,hi,show 0 < codeV c from hb.1]

lemma canonicalF_constant {m : ℕ} (c : PositiveCode m) :
    PowerSeries.constantCoeff (lift (canonicalF c)) = 0 := by
  apply lift_const_zero
  intro i hi
  have hb := code_bounds c
  simp [canonicalF,hi,show 0 < codeR c from hb.2.2.1,
    show 0 < codeCut c from hb.2.2.2.2.2]

#print axioms canonicalG_factor

lemma square_congr_zero_iff (r : ℕ) (d : Series) :
    Congr r (d^2) 0 ↔ Congr (r-r/2) d 0 := by
  constructor
  · intro h
    apply congr_iff.mpr
    intro i hi
    simp only [map_zero]
    by_contra hn
    have hd := PowerSeries.order_le i hn
    have hpow : (r : ℕ∞) ≤ (d*d).order := by
      apply PowerSeries.nat_le_order
      intro j hj
      simpa only [pow_two, map_zero] using congr_iff.mp h j hj
    rw [PowerSeries.order_mul] at hpow
    have hh : (r : ℕ∞) ≤ (i : ℕ∞)+(i : ℕ∞) :=
      hpow.trans (add_le_add hd hd)
    have hh' : r ≤ i+i := by exact_mod_cast hh
    omega
  · intro h
    apply congr_iff.mpr
    intro i hi
    simp only [map_zero]
    apply PowerSeries.coeff_of_lt_order
    have hd : ((r-r/2 : ℕ) : ℕ∞) ≤ d.order := by
      apply PowerSeries.nat_le_order
      intro j hj
      simpa only [map_zero] using congr_iff.mp h j hj
    rw [pow_two, PowerSeries.order_mul]
    have hh : (i : ℕ∞) < ((r-r/2 : ℕ) : ℕ∞)+((r-r/2 : ℕ) : ℕ∞) := by
      exact_mod_cast (show i < (r-r/2)+(r-r/2) by omega)
    exact hh.trans_le (add_le_add hd hd)

lemma canonicalF_low {m : ℕ} (c : PositiveCode m) :
    Congr (codeCut c) (lift (canonicalF c)) PowerSeries.X := by
  apply congr_iff.mpr
  intro i hi
  have hb := code_bounds c
  have hir : i < codeR c := by dsimp [codeCut] at hi; omega
  have him : i < m := by omega
  simp only [lift,PowerSeries.coeff_mk,dite_eq_left him]
  change canonicalF c ⟨i,him⟩ = PowerSeries.coeff i PowerSeries.X
  unfold canonicalF
  rw [dite_eq_left hir, dite_eq_left hi]
  simp [PowerSeries.coeff_X]

lemma canonical_obstruction {m : ℕ} (c : PositiveCode m) :
    Congr m (((1+PowerSeries.X)*lift (canonicalG c)) *
      (lift (canonicalF c)-PowerSeries.X)^2) 0 := by
  have hb := code_bounds c
  have hlow : Congr (codeCut c) (lift (canonicalF c)-PowerSeries.X) 0 := by
    apply congr_iff.mpr
    intro i hi
    simp only [map_sub,map_zero,sub_eq_zero]
    exact congr_iff.mp (canonicalF_low c) i hi
  have hsq := (square_congr_zero_iff (codeR c) _).mpr hlow
  have hh := congr_mul (show Congr (codeR c) (canonicalU c) (canonicalU c) from rfl) hsq
  have hshift : Congr m (PowerSeries.X^(codeV c)*(canonicalU c *
      (lift (canonicalF c)-PowerSeries.X)^2)) 0 := by
    have he : m-codeV c = codeR c := by omega
    have hh' := (congr_shift (m := m) (v := codeV c)).mpr (by simpa only [he] using hh)
    simpa only [mul_zero] using hh'
  have hg := congr_mul (canonicalG_factor c)
    (show Congr m ((lift (canonicalF c)-PowerSeries.X)^2)
      ((lift (canonicalF c)-PowerSeries.X)^2) from rfl)
  have hz : Congr m (lift (canonicalG c)*(lift (canonicalF c)-PowerSeries.X)^2) 0 :=
    hg.trans (by simpa only [mul_assoc] using hshift)
  have ht := congr_mul (show Congr m (1+PowerSeries.X) (1+PowerSeries.X) from rfl) hz
  simpa only [mul_zero,mul_assoc] using ht

/-- La suffisance ne demande aucune colonne 2, donc vaut aussi pour m≤2. -/
lemma normalized_complement_sufficient (m : ℕ) (g f : Series)
    (hg : PowerSeries.constantCoeff g=0) (hf : PowerSeries.constantCoeff f=0)
    (hobs : Congr m (((1+PowerSeries.X)*g)*(f-PowerSeries.X)^2) 0) :
    ∃ k : Series, PowerSeries.constantCoeff k=0 ∧ ∀ j < m,
      Congr m ((1+(1+PowerSeries.X)*g)*k^j)
        (((1+PowerSeries.X)*g)*f^j+PowerSeries.X^j) := by
  let G := (1+PowerSeries.X)*g
  let H := 1+G
  have hunit : IsUnit H := by
    apply PowerSeries.isUnit_iff_constantCoeff.mpr
    simp [H,G,hg]
  have hHq : quotientMap m H=1+quotientMap m G := by simp [H]
  obtain ⟨u, hu⟩ := hunit
  let k : Series := (↑(u⁻¹) : Series) * (G * f + PowerSeries.X)
  have h1 : H * k = G * f + PowerSeries.X := by
    calc H * k = ((u : Series) * (↑(u⁻¹) : Series)) * (G * f + PowerSeries.X) := by
            rw [hu]; ring
         _ = G * f + PowerSeries.X := by simp
  have hk : PowerSeries.constantCoeff k = 0 := by
    have hc := congrArg PowerSeries.constantCoeff h1
    simpa [H, G, hg, hf] using hc
  refine ⟨k, hk, ?_⟩
  have h1q := congrArg (quotientMap m) h1
  simp only [map_mul, map_add] at h1q
  have hobsq := (quotient_eq_iff _ _).mpr hobs
  simp only [map_mul, map_sub, map_pow, map_zero] at hobsq
  have hall := RiordanCore.all_columns hHq (IsUnit.map (quotientMap m) ⟨u, hu⟩) h1q hobsq
  intro j hj
  apply (quotient_eq_iff _ _).mp
  simpa only [H,G,map_one,map_mul, map_add, map_pow] using hall j


lemma canonicalMatrix_mem (m : ℕ) (hm : 0 < m) (c : PositiveCode m) :
    canonicalMatrix m c ∈ positiveSolutions m hm := by
  have hRep : Represents (canonicalMatrix m c) (lift (canonicalG c))
      (lift (canonicalF c)) := matrix_entry _ _
  have hR : canonicalMatrix m c ∈ riordanMatrices m :=
    (mem_riordan_iff _).mpr ⟨_,_,canonicalF_constant c,hRep⟩
  have hC : complement (canonicalMatrix m c) ∈ riordanMatrices m := by
    apply (complement_normalized_iff hm hRep).mpr
    exact normalized_complement_sufficient m _ _
      (canonicalG_constant c) (canonicalF_constant c) (canonical_obstruction c)
  apply Finset.mem_filter.mpr
  refine ⟨(mem_solutions _).mpr ⟨hR,hC⟩,?_,?_⟩
  · change (canonicalMatrix m c)[(⟨0,hm⟩ : Fin m)][(⟨0,hm⟩ : Fin m)] = 0
    rw [canonical_first_column]
    simp [canonicalG,(code_bounds c).1]
  · intro hz
    have hb := code_bounds c
    have hcol := canonical_first_column c hm ⟨codeV c,hb.2.1⟩
    rw [hz] at hcol
    simp [zeroMat,canonicalG] at hcol
#print axioms canonicalMatrix_mem

lemma canonical_index_eq {m : ℕ} (c d : PositiveCode m)
    (hG : canonicalG c = canonicalG d) : c.1=d.1 := by
  have hc := code_bounds c
  have hd := code_bounds d
  have hv : codeV c = codeV d := by
    rcases lt_trichotomy (codeV c) (codeV d) with hlt | heq | hgt
    · have hh := congrFun hG ⟨codeV c,hc.2.1⟩
      simp [canonicalG,hlt] at hh
    · exact heq
    · have hh := congrFun hG ⟨codeV d,hd.2.1⟩
      simp [canonicalG,hgt] at hh
  apply Fin.ext
  dsimp [codeV,codeR] at hv hc hd
  omega

lemma canonicalMatrix_injective (m : ℕ) : Function.Injective (canonicalMatrix m) := by
  intro c d he
  have hb := code_bounds c
  have hm : 0 < m := by omega
  have hG : canonicalG c = canonicalG d := by
    funext i
    have hh := congrArg (fun R : Mat m => R[i][(⟨0,hm⟩ : Fin m)]) he
    simpa only [canonical_first_column] using hh
  have hindex := canonical_index_eq c d hG
  rcases c with ⟨ic,uc,fc⟩
  rcases d with ⟨id,ud,fd⟩
  change ic=id at hindex
  subst id
  have hu : uc=ud := by
    funext k
    let v := m-(ic.val+1)
    have hi : v+k.val+1 < m := by have hk:=k.isLt; have hic:=ic.isLt; dsimp [v]; omega
    have hh := congrFun hG ⟨v+k.val+1,hi⟩
    have hlo : ¬v+k.val+1< v := by omega
    have heq : ¬v+k.val+1=v := by omega
    have hk : v+k.val+1-v-1=k.val := by omega
    dsimp only [canonicalG,codeV,codeR] at hh
    dsimp [v] at hh hlo heq hk
    simpa [hlo,heq,hk] using hh
  subst ud
  have hf : fc=fd := by
    let c : PositiveCode m := ⟨ic,uc,fc⟩
    let d : PositiveCode m := ⟨ic,uc,fd⟩
    have hm2 : 1 < m := by have hic:=ic.isLt; omega
    have hcols : Congr m (lift (canonicalG c)*lift (canonicalF c))
        (lift (canonicalG c)*lift (canonicalF d)) := by
      apply congr_iff.mpr
      intro i hi
      have hh := congrArg (fun R : Mat m => R[(⟨i,hi⟩ : Fin m)][(⟨1,hm2⟩ : Fin m)]) he
      simp only [canonicalMatrix,matrix_entry,pow_one] at hh
      have hgcd : canonicalG d=canonicalG c := by funext k; rfl
      change PowerSeries.coeff i (lift (canonicalG c)*lift (canonicalF c)) =
        PowerSeries.coeff i (lift (canonicalG d)*lift (canonicalF d)) at hh
      rwa [hgcd] at hh
    have hleft := congr_mul (canonicalG_factor c)
      (show Congr m (lift (canonicalF c)) (lift (canonicalF c)) from rfl)
    have hright := congr_mul (canonicalG_factor c)
      (show Congr m (lift (canonicalF d)) (lift (canonicalF d)) from rfl)
    have hh := hleft.symm.trans (hcols.trans hright)
    have hs : Congr (codeR c) (canonicalU c*lift (canonicalF c))
        (canonicalU c*lift (canonicalF d)) := by
      have hv : m-codeV c=codeR c := by have hb:=code_bounds c;omega
      simpa only [hv] using (congr_shift (m:=m) (v:=codeV c)).mp
        (by simpa only [mul_assoc] using hh)
    have hfcon := (congr_cancel_unit (canonicalU_unit c)).mp hs
    funext k
    let cut := codeCut c
    have hk : cut+k.val< codeR c := by
      have hki:=k.isLt; dsimp [cut,codeCut,codeR,c] at *;omega
    have him : cut+k.val< m := by have hb:=code_bounds c;omega
    have hhf := congr_iff.mp hfcon (cut+k.val) hk
    have hcut : ¬cut+k.val< cut := by omega
    have hsub : cut+k.val-cut=k.val := by omega
    dsimp [cut,codeCut,codeR,c] at hk him hcut hsub
    dsimp only [c,d,cut,canonicalF,codeCut,codeR,lift] at hhf
    simpa only [PowerSeries.coeff_mk,dite_eq_left him,
      dite_eq_left hk,dite_eq_right hcut,hsub] using hhf
  subst fd
  rfl

#print axioms canonicalMatrix_injective

/-- Une représentation quelconque admet un premier coefficient non nul avant m. -/
lemma positive_leading_term {m : ℕ} (hm : 0 < m) (R : Mat m)
    (hR : R ∈ positiveSolutions m hm) :
    ∃ (g f : Series) (v : ℕ) (u : Series),
      PowerSeries.constantCoeff f=0 ∧ Represents R g f ∧
      0 < v ∧ v < m ∧ g=PowerSeries.X^v*u ∧
      PowerSeries.constantCoeff u=1 := by
  obtain ⟨hS,htop,hne⟩ := Finset.mem_filter.mp hR
  obtain ⟨g,f,hf,hRep⟩ := (mem_riordan_iff _).mp ((mem_solutions _).mp hS).1
  have hg0 : PowerSeries.constantCoeff g=0 := by
    have hh := hRep ⟨0,hm⟩ ⟨0,hm⟩
    change R[(⟨0,hm⟩ : Fin m)][(⟨0,hm⟩ : Fin m)] = _ at hh
    change R[(⟨0,hm⟩ : Fin m)][(⟨0,hm⟩ : Fin m)] = 0 at htop
    simpa using hh.symm.trans htop
  have hex : ∃ v : ℕ, v < m ∧ PowerSeries.coeff v g ≠ 0 := by
    by_contra hn
    push Not at hn
    apply hne
    apply zero_of_first_column hm R ((mem_solutions _).mp hS).1
    intro i
    rw [hRep]
    simpa using hn i.val i.isLt
  let v := Nat.find hex
  have hv := Nat.find_spec hex
  change v < m ∧ PowerSeries.coeff v g ≠ 0 at hv
  have hlow : ∀ i < v, PowerSeries.coeff i g=0 := by
    intro i hi
    by_contra hn
    have hh := Nat.find_min' hex (show i< m ∧ PowerSeries.coeff i g≠0 from ⟨by omega,hn⟩)
    change v≤ i at hh
    omega
  have hvpos : 0 < v := by
    by_contra hn
    have he : v=0 := by omega
    have hh := hv.2
    simp [he,PowerSeries.coeff_zero_eq_constantCoeff,hg0] at hh
  have hone : PowerSeries.coeff v g=1 := (binary_cases _).resolve_left hv.2
  obtain ⟨u,hu⟩ := PowerSeries.X_pow_dvd_iff.mpr hlow
  have hu0 : PowerSeries.constantCoeff u=1 := by
    have hh := congrArg (PowerSeries.coeff v) hu
    rw [hone,PowerSeries.coeff_X_pow_mul'] at hh
    simpa using hh.symm
  exact ⟨g,f,v,u,hf,hRep,hvpos,hv.1,hu,hu0⟩

/-- Nécessité de la coupure sur f, avec traitement explicite des petites tailles. -/
lemma positive_f_low {m v : ℕ} (hm : 0 < m) (hv : 0 < v) (hvm : v < m)
    {R : Mat m} {g f u : Series} (hS : R ∈ solutions m)
    (hf : PowerSeries.constantCoeff f=0) (hRep : Represents R g f)
    (hg : g=PowerSeries.X^v*u) (hu0 : PowerSeries.constantCoeff u=1) :
    Congr ((m-v)-(m-v)/2) f PowerSeries.X := by
  by_cases hm3 : 3 ≤ m
  · have hg0 : PowerSeries.constantCoeff g=0 := by simp [hg,ne_of_gt hv]
    have hnorm := (complement_normalized_iff hm hRep).mp ((mem_solutions _).mp hS).2
    have hobs := (normalized_complement_criterion m hm3 g f hg0 hf).mp hnorm
    have hunit : IsUnit ((1+PowerSeries.X)*u) := by
      apply PowerSeries.isUnit_iff_constantCoeff.mpr
      simp [hu0]
    have hs : Congr (m-v) (((1+PowerSeries.X)*u)*(f-PowerSeries.X)^2) 0 := by
      apply (congr_shift (m:=m) (v:=v)).mp
      simpa only [hg,mul_assoc,mul_left_comm,mul_comm,mul_zero,zero_mul] using hobs
    have hd : Congr (m-v) ((f-PowerSeries.X)^2) 0 := by
      apply (congr_cancel_unit hunit).mp
      simpa only [mul_zero] using hs
    have hl := (square_congr_zero_iff (m-v) _).mp hd
    apply congr_iff.mpr
    intro i hi
    have hh := congr_iff.mp hl i hi
    simpa only [map_sub,map_zero,sub_eq_zero] using hh
  · have hr : m-v=1 := by omega
    rw [hr]
    apply congr_iff.mpr
    intro i hi
    have hi0 : i=0 := by omega
    simp [hi0,PowerSeries.coeff_zero_eq_constantCoeff,hf]

#print axioms positive_leading_term
#print axioms positive_f_low

/-- Lecture des queues à partir d'une représentation, sans hypothèse d'unicité. -/
noncomputable def codeOfSeries (m v : ℕ) (hv : 0 < v) (hvm : v < m)
    (g f : Series) : PositiveCode m :=
  ⟨⟨m-v-1,by omega⟩,
    (fun k => PowerSeries.coeff (v+k.val+1) g),
    (fun k => PowerSeries.coeff ((m-v)-(m-v)/2+k.val) f)⟩

lemma codeOfSeries_r (m v : ℕ) (hv : 0 < v) (hvm : v < m) (g f : Series) :
    codeR (codeOfSeries m v hv hvm g f)=m-v := by
  dsimp [codeR,codeOfSeries]
  omega

lemma codeOfSeries_v (m v : ℕ) (hv : 0 < v) (hvm : v < m) (g f : Series) :
    codeV (codeOfSeries m v hv hvm g f)=v := by
  rw [codeV,codeOfSeries_r]
  omega

lemma codeOfSeries_g (m v : ℕ) (hv : 0 < v) (hvm : v < m) (g f u : Series)
    (hg : g=PowerSeries.X^v*u) (hu0 : PowerSeries.constantCoeff u=1) :
    Congr m (lift (canonicalG (codeOfSeries m v hv hvm g f))) g := by
  let c := codeOfSeries m v hv hvm g f
  have hcv := codeOfSeries_v m v hv hvm g f
  apply congr_iff.mpr
  intro i hi
  simp only [lift,PowerSeries.coeff_mk,dite_eq_left hi]
  change canonicalG c ⟨i,hi⟩ = PowerSeries.coeff i g
  unfold canonicalG
  change codeV c=v at hcv
  simp only [hcv]
  by_cases hlo : i < v
  · simp [hlo,hg,PowerSeries.coeff_X_pow_mul',show ¬v ≤ i by omega]
  · by_cases heq : i=v
    · subst i
      simp [hg,PowerSeries.coeff_X_pow_mul',hu0,PowerSeries.coeff_zero_eq_constantCoeff]
    · rw [dite_eq_right hlo,dite_eq_right heq]
      change PowerSeries.coeff (v+(i-v-1)+1) g = PowerSeries.coeff i g
      exact congrArg (fun k => PowerSeries.coeff k g) (by omega)

lemma codeOfSeries_f (m v : ℕ) (hv : 0 < v) (hvm : v < m) (g f : Series)
    (hlow : Congr ((m-v)-(m-v)/2) f PowerSeries.X) :
    Congr (m-v) (lift (canonicalF (codeOfSeries m v hv hvm g f))) f := by
  let c := codeOfSeries m v hv hvm g f
  have hcr := codeOfSeries_r m v hv hvm g f
  have hcut : codeCut c=(m-v)-(m-v)/2 := by dsimp [codeCut];rw [hcr]
  change codeR c=m-v at hcr
  apply congr_iff.mpr
  intro i hi
  have him : i < m := by omega
  simp only [lift,PowerSeries.coeff_mk,dite_eq_left him]
  change canonicalF c ⟨i,him⟩ = PowerSeries.coeff i f
  unfold canonicalF
  simp only [hcr,hcut,dite_eq_left hi]
  by_cases hlo : i < (m-v)-(m-v)/2
  · rw [dite_eq_left hlo]
    simpa only [PowerSeries.coeff_X] using (congr_iff.mp hlow i hlo).symm
  · rw [dite_eq_right hlo]
    change PowerSeries.coeff ((m-v)-(m-v)/2+(i-((m-v)-(m-v)/2))) f = PowerSeries.coeff i f
    exact congrArg (fun k => PowerSeries.coeff k f) (by omega)

lemma matrix_reconstruction {m v : ℕ} (R : Mat m) (g f u : Series)
    (hRep : Represents R g f) (hg : g=PowerSeries.X^v*u)
    (g' f' : Jet m) (hcg : Congr m (lift g') g) (hcf : Congr (m-v) (lift f') f) :
    riordanMatrix g' f'=R := by
  apply Vector.ext
  intro i hi
  apply Vector.ext
  intro j hj
  have hc := congr_mul hcg (show Congr m (lift f'^j) (lift f'^j) from rfl)
  have ht := congr_mul (show Congr (m-v) u u from rfl) (congr_pow hcf j)
  have hs := (congr_shift (m:=m) (v:=v)).mpr ht
  have hh : Congr m (g*lift f'^j) (g*f^j) := by
    simpa only [hg,mul_assoc] using hs
  have he := congr_iff.mp (hc.trans hh) i hi
  calc (riordanMatrix g' f')[i][j] = PowerSeries.coeff i (lift g'*lift f'^j) :=
          matrix_entry g' f' ⟨i,hi⟩ ⟨j,hj⟩
       _ = PowerSeries.coeff i (g*f^j) := he
       _ = R[i][j] := (hRep ⟨i,hi⟩ ⟨j,hj⟩).symm

lemma positiveSolutions_subset_image (m : ℕ) (hm : 0 < m) :
    positiveSolutions m hm ⊆ (Finset.univ : Finset (PositiveCode m)).image (canonicalMatrix m) := by
  intro R hR
  obtain ⟨g,f,v,u,hf,hRep,hv,hvm,hg,hu0⟩ := positive_leading_term hm R hR
  have hS := (Finset.mem_filter.mp hR).1
  have hlow := positive_f_low hm hv hvm hS hf hRep hg hu0
  apply Finset.mem_image.mpr
  refine ⟨codeOfSeries m v hv hvm g f, Finset.mem_univ _, ?_⟩
  exact matrix_reconstruction R g f u hRep hg _ _
    (codeOfSeries_g m v hv hvm g f u hg hu0)
    (codeOfSeries_f m v hv hvm g f hlow)

#print axioms positiveSolutions_subset_image

lemma positiveSolutions_eq_image (m : ℕ) (hm : 0 < m) :
    positiveSolutions m hm =
      (Finset.univ : Finset (PositiveCode m)).image (canonicalMatrix m) := by
  apply Finset.Subset.antisymm (positiveSolutions_subset_image m hm)
  intro R hR
  obtain ⟨c,_,rfl⟩ := Finset.mem_image.mp hR
  exact canonicalMatrix_mem m hm c

lemma card_positiveCode (m : ℕ) :
    Fintype.card (PositiveCode m) =
      ∑ i ∈ Finset.range (m - 1), 2 ^ (i + (i + 1) / 2) := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, ZMod.card]
  simp_rw [← pow_add]
  exact Fin.sum_univ_eq_sum_range (fun i : ℕ => (2 : ℕ) ^ (i + (i + 1) / 2)) (m - 1)

lemma card_positiveSolutions (m : ℕ) (hm : 0 < m) :
    (positiveSolutions m hm).card =
      ∑ i ∈ Finset.range (m - 1), 2 ^ (i + (i + 1) / 2) := by
  rw [positiveSolutions_eq_image m hm,
    Finset.card_image_of_injective _ (canonicalMatrix_injective m),
    Finset.card_univ,card_positiveCode]

lemma double_term (i : ℕ) :
    2 * 2 ^ (i + (i + 1) / 2) = 2 ^ (3 * (i + 1) / 2) := by
  rw [← pow_succ']
  congr 1
  omega

/-- Dénombrement exact des matrices distinctes dont le complément est de Riordan. -/
theorem A401496_formula (n : ℕ) (hn : 0 < n) :
    a n = 1 + ∑ k ∈ Finset.range (n - 1), 2 ^ (3 * k / 2) := by
  by_cases hn1 : n = 1
  · subst n
    decide
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    have hm : 0 < m := by omega
    have hc := card_solutions_two_add_twice hm
    rw [card_positiveSolutions] at hc
    have hs := Finset.sum_range_succ' (fun k => (2 : ℕ) ^ (3 * k / 2)) (m - 1)
    rw [Nat.sub_add_cancel hm] at hs
    simp only [Nat.mul_zero, Nat.zero_div, pow_zero] at hs
    have hd : 2 * ∑ i ∈ Finset.range (m - 1), 2 ^ (i + (i + 1) / 2) =
        ∑ i ∈ Finset.range (m - 1), 2 ^ (3 * (i + 1) / 2) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      exact double_term i
    change (solutions m).card = 1 + ∑ k ∈ Finset.range m, 2 ^ (3 * k / 2)
    omega

#print axioms card_positiveCode
#print axioms A401496_formula
end A401496

#eval (List.range' 1 6).map A401496.a
