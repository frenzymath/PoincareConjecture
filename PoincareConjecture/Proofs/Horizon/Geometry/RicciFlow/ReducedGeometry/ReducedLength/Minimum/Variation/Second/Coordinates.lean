import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variation.Geometry.Coordinates

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace PoincareConjecture.ReducedLengthMinimum.Variation.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

local instance secondVariationCoordinatesDualGroup : NormedAddCommGroup (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance secondVariationCoordinatesDualSpace : NormedSpace ℝ (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace
local instance secondVariationCoordinatesBilinGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance secondVariationCoordinatesBilinSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace
local instance secondVariationCoordinatesEndGroup : NormedAddCommGroup (E →L[ℝ] E) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance secondVariationCoordinatesEndSpace : NormedSpace ℝ (E →L[ℝ] E) :=
  ContinuousLinearMap.toNormedSpace
local instance secondVariationCoordinatesConnectionGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance secondVariationCoordinatesConnectionSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E) :=
  ContinuousLinearMap.toNormedSpace

def coordinatePartialS (f : ℝ × ℝ → E) (p : ℝ × ℝ) : E := fderiv ℝ f p (1, 0)

def coordinatePartialU (f : ℝ × ℝ → E) (p : ℝ × ℝ) : E := fderiv ℝ f p (0, 1)

theorem coordinatePartialS_contDiffOn {Ω : Set (ℝ × ℝ)} (hΩ : IsOpen Ω)
    (f : ℝ × ℝ → E) (hf : ContDiffOn ℝ ∞ f Ω) :
    ContDiffOn ℝ ∞ (coordinatePartialS f) Ω :=
  (hf.fderiv_of_isOpen hΩ (m := ∞) (by simp)).clm_apply contDiffOn_const

theorem coordinatePartialU_contDiffOn {Ω : Set (ℝ × ℝ)} (hΩ : IsOpen Ω)
    (f : ℝ × ℝ → E) (hf : ContDiffOn ℝ ∞ f Ω) :
    ContDiffOn ℝ ∞ (coordinatePartialU f) Ω :=
  (hf.fderiv_of_isOpen hΩ (m := ∞) (by simp)).clm_apply contDiffOn_const

theorem coordinatePartials_commute (f : ℝ × ℝ → E) {p : ℝ × ℝ}
    (hf : ContDiffAt ℝ ∞ f p) :
    coordinatePartialU (coordinatePartialS f) p =
      coordinatePartialS (coordinatePartialU f) p := by
  have hD := ((hf.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)).hasFDerivAt
  have hS := (hD.clm_apply (hasFDerivAt_const ((1 : ℝ), (0 : ℝ)) p)).fderiv
  have hU := (hD.clm_apply (hasFDerivAt_const ((0 : ℝ), (1 : ℝ)) p)).fderiv
  change fderiv ℝ (coordinatePartialS f) p = _ at hS
  change fderiv ℝ (coordinatePartialU f) p = _ at hU
  change fderiv ℝ (coordinatePartialS f) p (0, 1) =
    fderiv ℝ (coordinatePartialU f) p (1, 0)
  rw [hS, hU]
  simp only [add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.zero_apply,
    map_zero, zero_add, ContinuousLinearMap.flip_apply]
  have htwo : minSmoothness ℝ 2 ≤ (∞ : ℕ∞ω) := by
    rw [minSmoothness_of_isRCLikeNormedField]
    change (↑(2 : ℕ∞) : ℕ∞ω) ≤ ↑(⊤ : ℕ∞)
    exact WithTop.coe_le_coe.mpr le_top
  exact (hf.isSymmSndFDerivAt htwo) (0, 1) (1, 0)

def coordinateCovariantS (Γ : ℝ × E → E →L[ℝ] E →L[ℝ] E)
    (q W : ℝ × ℝ → E) (p : ℝ × ℝ) : E :=
  coordinatePartialS W p + Γ (p.1, q p) (coordinatePartialS q p) (W p)

def coordinateCovariantU (Γ : ℝ × E → E →L[ℝ] E →L[ℝ] E)
    (q W : ℝ × ℝ → E) (p : ℝ × ℝ) : E :=
  coordinatePartialU W p + Γ (p.1, q p) (coordinatePartialU q p) (W p)

theorem coordinateCovariant_torsion (Γ : ℝ × E → E →L[ℝ] E →L[ℝ] E)
    (q : ℝ × ℝ → E) {p : ℝ × ℝ} (hq : ContDiffAt ℝ ∞ q p)
    (hΓ : ∀ v w : E, Γ (p.1, q p) v w = Γ (p.1, q p) w v) :
    coordinateCovariantU Γ q (coordinatePartialS q) p =
      coordinateCovariantS Γ q (coordinatePartialU q) p := by
  unfold coordinateCovariantU coordinateCovariantS
  rw [coordinatePartials_commute q hq, hΓ]

set_option maxHeartbeats 1200000 in
theorem coordinateCovariant_commutator (Γ : ℝ × E → E →L[ℝ] E →L[ℝ] E)
    (q W : ℝ × ℝ → E) {p : ℝ × ℝ}
    (hq : ContDiffAt ℝ ∞ q p) (hW : ContDiffAt ℝ ∞ W p)
    (hΓ : DifferentiableAt ℝ Γ (p.1, q p)) :
    coordinateCovariantU Γ q (coordinateCovariantS Γ q W) p -
        coordinateCovariantS Γ q (coordinateCovariantU Γ q W) p =
      fderiv ℝ Γ (p.1, q p) (0, coordinatePartialU q p) (coordinatePartialS q p) (W p) -
      fderiv ℝ Γ (p.1, q p) (0, coordinatePartialS q p) (coordinatePartialU q p) (W p) +
      Γ (p.1, q p) (coordinatePartialU q p)
        (Γ (p.1, q p) (coordinatePartialS q p) (W p)) -
      Γ (p.1, q p) (coordinatePartialS q p)
        (Γ (p.1, q p) (coordinatePartialU q p) (W p)) -
      fderiv ℝ Γ (p.1, q p) (1, 0) (coordinatePartialU q p) (W p) := by
  have hdq := (hq.differentiableAt (by simp)).hasFDerivAt
  have hdW := (hW.differentiableAt (by simp)).hasFDerivAt
  have hdDq := ((hq.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)).hasFDerivAt
  have hdDW := ((hW.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)).hasFDerivAt
  have hA := hdDq.clm_apply (hasFDerivAt_const ((1 : ℝ), (0 : ℝ)) p)
  have hY := hdDq.clm_apply (hasFDerivAt_const ((0 : ℝ), (1 : ℝ)) p)
  have hSW := hdDW.clm_apply (hasFDerivAt_const ((1 : ℝ), (0 : ℝ)) p)
  have hUW := hdDW.clm_apply (hasFDerivAt_const ((0 : ℝ), (1 : ℝ)) p)
  have hk : HasFDerivAt (fun z : ℝ × ℝ ↦ (z.1, q z))
      ((ContinuousLinearMap.fst ℝ ℝ ℝ).prod (fderiv ℝ q p)) p :=
    hasFDerivAt_fst.prodMk hdq
  have hL : HasFDerivAt (fun z : ℝ × ℝ ↦ Γ (z.1, q z))
      ((fderiv ℝ Γ (p.1, q p)).comp
        ((ContinuousLinearMap.fst ℝ ℝ ℝ).prod (fderiv ℝ q p))) p :=
    hΓ.hasFDerivAt.comp (f := fun z : ℝ × ℝ ↦ (z.1, q z)) p hk
  have hS := (hSW.add ((hL.clm_apply hA).clm_apply hdW)).fderiv
  have hU := (hUW.add ((hL.clm_apply hY).clm_apply hdW)).fderiv
  change fderiv ℝ (coordinateCovariantS Γ q W) p = _ at hS
  change fderiv ℝ (coordinateCovariantU Γ q W) p = _ at hU
  have hmixq := coordinatePartials_commute q hq
  have hmixW := coordinatePartials_commute W hW
  have heq : ((1 : ℝ), coordinatePartialS q p) =
      (1, (0 : E)) + (0, coordinatePartialS q p) := by simp
  change fderiv ℝ (coordinateCovariantS Γ q W) p (0, 1) +
      Γ (p.1, q p) (coordinatePartialU q p) (coordinateCovariantS Γ q W p) -
    (fderiv ℝ (coordinateCovariantU Γ q W) p (1, 0) +
      Γ (p.1, q p) (coordinatePartialS q p) (coordinateCovariantU Γ q W p)) = _
  rw [hS, hU]
  simp only [add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.zero_apply, ContinuousLinearMap.prod_apply,
    map_zero, zero_add, add_zero]
  change fderiv ℝ (fderiv ℝ W) p (0, 1) (1, 0) +
      (Γ (p.1, q p) (coordinatePartialS q p) (coordinatePartialU W p) +
        (Γ (p.1, q p) (fderiv ℝ (fderiv ℝ q) p (0, 1) (1, 0)) +
          fderiv ℝ Γ (p.1, q p) (0, coordinatePartialU q p) (coordinatePartialS q p)) (W p)) +
      Γ (p.1, q p) (coordinatePartialU q p) (coordinateCovariantS Γ q W p) -
    (fderiv ℝ (fderiv ℝ W) p (1, 0) (0, 1) +
      (Γ (p.1, q p) (coordinatePartialU q p) (coordinatePartialS W p) +
        (Γ (p.1, q p) (fderiv ℝ (fderiv ℝ q) p (1, 0) (0, 1)) +
          fderiv ℝ Γ (p.1, q p) (1, coordinatePartialS q p) (coordinatePartialU q p)) (W p)) +
      Γ (p.1, q p) (coordinatePartialS q p) (coordinateCovariantU Γ q W p)) = _
  have htwo : minSmoothness ℝ 2 ≤ (∞ : ℕ∞ω) := by
    rw [minSmoothness_of_isRCLikeNormedField]
    change (↑(2 : ℕ∞) : ℕ∞ω) ≤ ↑(⊤ : ℕ∞)
    exact WithTop.coe_le_coe.mpr le_top
  rw [(hW.isSymmSndFDerivAt htwo) (0, 1) (1, 0),
    (hq.isSymmSndFDerivAt htwo) (0, 1) (1, 0), heq]
  simp only [coordinateCovariantS, coordinateCovariantU, map_add, add_apply]
  abel

theorem chart_pair_covariant_hasDerivAt
    (G : E → E →L[ℝ] E →L[ℝ] ℝ) (Γ : E →L[ℝ] E →L[ℝ] E)
    (DG : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
    {q A B : ℝ → E} {u : ℝ} {y a b : E}
    (hG : HasFDerivAt G DG (q u)) (hq : HasDerivAt q y u)
    (hA : HasDerivAt A a u) (hB : HasDerivAt B b u)
    (hcompat : DG y (A u) (B u) =
      G (q u) (Γ y (A u)) (B u) + G (q u) (A u) (Γ y (B u))) :
    HasDerivAt (fun r ↦ G (q r) (A r) (B r))
      (G (q u) (a + Γ y (A u)) (B u) + G (q u) (A u) (b + Γ y (B u))) u := by
  have h := ((hG.comp_hasDerivAt u hq).clm_apply hA).clm_apply hB
  convert h using 1 <;> try rfl
  simp only [map_add, add_apply, Function.comp_def]
  linarith

theorem chart_pair_moving_covariant_hasDerivAt
    (G : ℝ → E →L[ℝ] E →L[ℝ] ℝ) (Γ : E →L[ℝ] E →L[ℝ] E)
    (H DG : E →L[ℝ] E →L[ℝ] ℝ)
    {Y Z : ℝ → E} {s : ℝ} {a y z : E}
    (hG : HasDerivAt G DG s) (hY : HasDerivAt Y y s) (hZ : HasDerivAt Z z s)
    (hcompat : DG (Y s) (Z s) =
      G s (Γ a (Y s)) (Z s) + G s (Y s) (Γ a (Z s)) + H (Y s) (Z s)) :
    HasDerivAt (fun r ↦ G r (Y r) (Z r))
      (G s (y + Γ a (Y s)) (Z s) + G s (Y s) (z + Γ a (Z s)) + H (Y s) (Z s)) s := by
  have h := (hG.clm_apply hY).clm_apply hZ
  convert h using 1 <;> try rfl
  simp only [map_add, add_apply]
  linarith

end PoincareConjecture.ReducedLengthMinimum.Variation.Geometry
