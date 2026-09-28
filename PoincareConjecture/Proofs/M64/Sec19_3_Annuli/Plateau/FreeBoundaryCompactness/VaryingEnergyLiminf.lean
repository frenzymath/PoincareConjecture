import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.VariableModulusLiminf













set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped Topology Manifold ContDiff

namespace PoincareConjecture.M64

open Poincare.Analysis.Sobolev.WeakCompactness

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]

local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "S" => interior m64AnnulusDomain
local notation "mu" => volume.restrict S




theorem varying_trace_column_energy_le_liminf
    {e : M → E} (hei : IsEmbedding e) {c0 c1 : ℕ → ℝ → M} {d0 d1 : ℝ → M}
    (B : M → E →L[ℝ] E →L[ℝ] ℝ) (hB : Continuous B)
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ q, ‖B q‖ ≤ K)
    (hpos : ∀ q v, 0 ≤ B q v v) (hsymm : ∀ q v w, B q v w = B q w v)
    (A : ∀ j, M64ObservedWeakAnnulus (n := n) e (c0 j) (c1 j))
    (L : M64ObservedWeakAnnulus (n := n) e d0 d1) (i : Fin 2)
    {C : ℝ} (hC : ∀ j, ‖(A j).column i‖ ^ 2 ≤ C)
    (hweak : WeakConverges (fun j => (A j).column i) (L.column i))
    (hlim : ∀ᵐ p ∂mu, Tendsto (fun j => (A j).map p) atTop (𝓝 (L.map p))) :
    (∫ p in S, B (L.map p) (L.column i p) (L.column i p)) ≤
      liminf (fun j => ∫ p in S, B ((A j).map p) ((A j).column i p)
        ((A j).column i p)) atTop := by
  have hC0 : 0 ≤ C := (sq_nonneg ‖(A 0).column i‖).trans (hC 0)
  apply m64MovingQuadratic_le_liminf (fun j p => B ((A j).map p)) (fun p => B (L.map p))
    (fun j => hB.comp_aestronglyMeasurable ((A j).map_aestronglyMeasurable hei))
    (hB.comp_aestronglyMeasurable (L.map_aestronglyMeasurable hei)) hK
    (fun j => Eventually.of_forall fun p => hb ((A j).map p))
  · filter_upwards [hlim] with p hp
    exact (hB.tendsto _).comp hp
  · exact fun j => Eventually.of_forall fun p v => hpos ((A j).map p) v
  · exact fun j => Eventually.of_forall fun p v w => hsymm ((A j).map p) v w
  · exact hweak
  · intro j
    exact show ‖(A j).column i‖ ≤ Real.sqrt C by
      nlinarith [Real.sq_sqrt hC0, Real.sqrt_nonneg C, norm_nonneg ((A j).column i), hC j]




theorem varying_trace_weightedEnergy_le_liminf
    {e : M → E} (hei : IsEmbedding e) {c0 c1 : ℕ → ℝ → M} {d0 d1 : ℝ → M}
    (B : M → E →L[ℝ] E →L[ℝ] ℝ) (hB : Continuous B)
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ q, ‖B q‖ ≤ K)
    (hpos : ∀ q v, 0 ≤ B q v v) (hsymm : ∀ q v w, B q v w = B q w v)
    {lo hi r0 : ℝ} (hlo : 0 < lo) (hr0 : r0 ∈ Icc lo hi)
    (r : ℕ → ℝ) (hr : ∀ j, r j ∈ Icc lo hi) (hrlim : Tendsto r atTop (𝓝 r0))
    (A : ∀ j, M64ObservedWeakAnnulus (n := n) e (c0 j) (c1 j))
    (L : M64ObservedWeakAnnulus (n := n) e d0 d1)
    {C : ℝ} (hC : ∀ j i, ‖(A j).column i‖ ^ 2 ≤ C)
    (hweak : ∀ i, WeakConverges (fun j => (A j).column i) (L.column i))
    (hlim : ∀ᵐ p ∂mu, Tendsto (fun j => (A j).map p) atTop (𝓝 (L.map p))) :
    L.weightedEnergy B r0 ≤ liminf (fun j => (A j).weightedEnergy B (r j)) atTop := by
  let q : Fin 2 → ℕ → ℝ := fun i j =>
    ∫ p in S, B ((A j).map p) ((A j).column i p) ((A j).column i p)
  have hqnonneg (i : Fin 2) (j : ℕ) : 0 ≤ q i j := integral_nonneg fun p => hpos _ _
  have hqbound (i : Fin 2) (j : ℕ) : q i j ≤ K * C :=
    ((A j).column_energy_le_norm_sq B hB hei hb i).trans
      (mul_le_mul_of_nonneg_left (hC j i) hK)
  have hcol (i : Fin 2) :
      (∫ p in S, B (L.map p) (L.column i p) (L.column i p)) ≤ liminf (q i) atTop :=
    varying_trace_column_energy_le_liminf hei B hB hK hb hpos hsymm A L i
      (fun j => hC j i) (hweak i) hlim
  have hweighted (i : Fin 2) {w : ℕ → ℝ} {w0 W : ℝ}
      (hwlim : Tendsto w atTop (𝓝 w0)) (hw : ∀ j, 0 ≤ w j) (hw0 : 0 ≤ w0)
      (hwbound : ∀ j, w j ≤ W) :
      w0 * (∫ p in S, B (L.map p) (L.column i p) (L.column i p)) ≤
        liminf (fun j => w j * q i j) atTop := by
    have hh : liminf w atTop * liminf (q i) atTop ≤
        liminf (fun j => w j * q i j) atTop := le_liminf_mul (Eventually.of_forall hw)
      (isBoundedUnder_of_eventually_le (Eventually.of_forall hwbound))
      (Eventually.of_forall (hqnonneg i))
      (isBoundedUnder_of_eventually_le (Eventually.of_forall (hqbound i))).isCoboundedUnder_ge
    rw [hwlim.liminf_eq] at hh
    exact (mul_le_mul_of_nonneg_left (hcol i) hw0).trans hh
  have hrpos (j : ℕ) : 0 < r j := hlo.trans_le (hr j).1
  have hr0pos : 0 < r0 := hlo.trans_le hr0.1
  have hinv (j : ℕ) : (r j)⁻¹ ≤ lo⁻¹ := (inv_le_inv₀ (hrpos j) hlo).mpr (hr j).1
  let W := max hi lo⁻¹
  have hW : 0 ≤ W := ((hlo.le.trans hr0.1).trans hr0.2).trans (le_max_left _ _)
  have hw0 (j : ℕ) : r j / 2 ≤ W := by
    have hh := (hr j).2.trans (le_max_left hi lo⁻¹)
    dsimp only [W]
    linarith [hrpos j]
  have hw1 (j : ℕ) : (r j)⁻¹ / 2 ≤ W := by
    have hh := (hinv j).trans (le_max_right hi lo⁻¹)
    dsimp only [W]
    linarith [inv_pos.mpr (hrpos j)]
  have h0 := hweighted 0 (hrlim.div_const 2)
    (fun j => div_nonneg (hrpos j).le (by norm_num))
    (div_nonneg hr0pos.le (by norm_num)) hw0
  have h1 := hweighted 1 ((hrlim.inv₀ hr0pos.ne').div_const 2)
    (fun j => div_nonneg (inv_nonneg.mpr (hrpos j).le) (by norm_num))
    (div_nonneg (inv_nonneg.mpr hr0pos.le) (by norm_num)) hw1
  let f0 := fun j => (r j / 2) * q 0 j
  let f1 := fun j => ((r j)⁻¹ / 2) * q 1 j
  have hf0nonneg (j : ℕ) : 0 ≤ f0 j :=
    mul_nonneg (div_nonneg (hrpos j).le (by norm_num)) (hqnonneg 0 j)
  have hf1nonneg (j : ℕ) : 0 ≤ f1 j :=
    mul_nonneg (div_nonneg (inv_nonneg.mpr (hrpos j).le) (by norm_num)) (hqnonneg 1 j)
  have hf0bound (j : ℕ) : f0 j ≤ W * (K * C) :=
    mul_le_mul (hw0 j) (hqbound 0 j) (hqnonneg 0 j) hW
  have hf1bound (j : ℕ) : f1 j ≤ W * (K * C) :=
    mul_le_mul (hw1 j) (hqbound 1 j) (hqnonneg 1 j) hW
  have hsum (j : ℕ) : f0 j + f1 j = (A j).weightedEnergy B (r j) :=
    ((A j).weightedEnergy_eq_column_integrals B hB hei hb (r j)).symm
  calc
    _ = (r0 / 2) * (∫ p in S, B (L.map p) (L.column 0 p) (L.column 0 p)) +
        (r0⁻¹ / 2) * (∫ p in S, B (L.map p) (L.column 1 p) (L.column 1 p)) :=
      L.weightedEnergy_eq_column_integrals B hB hei hb r0
    _ ≤ liminf f0 atTop + liminf f1 atTop := add_le_add h0 h1
    _ ≤ liminf (fun j => f0 j + f1 j) atTop := le_liminf_add
      (isBoundedUnder_of_eventually_ge (Eventually.of_forall hf0nonneg))
      (isBoundedUnder_of_eventually_le (Eventually.of_forall hf0bound))
      (isBoundedUnder_of_eventually_ge (Eventually.of_forall hf1nonneg))
      (isBoundedUnder_of_eventually_le (Eventually.of_forall hf1bound)).isCoboundedUnder_ge
    _ = _ := by simp only [hsum]

end PoincareConjecture.M64
