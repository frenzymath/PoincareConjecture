import PoincareConjecture.Proofs.M64.Sec19_7_RampTransport.BoundaryBootstrapForcing











set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped ContDiff ENNReal

namespace PoincareConjecture.M64.RampTransport

open Poincare.Analysis.Sobolev
open Weak Euclidean WeakCompactness

local notation "Plane" => EuclideanSpace ℝ (Fin 2)
variable {n : ℕ}
local notation "Target" => EuclideanSpace ℝ (Fin n)

local instance : NormedAddCommGroup (Target →L[ℝ] Target →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (Target →L[ℝ] Target →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace
local instance : NormedAddCommGroup (Target →L[ℝ] Target →L[ℝ] Target →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (Target →L[ℝ] Target →L[ℝ] Target →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace
local instance : NormedAddCommGroup
    (Target →L[ℝ] Target →L[ℝ] Target →L[ℝ] Target →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ
    (Target →L[ℝ] Target →L[ℝ] Target →L[ℝ] Target →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace





def quadraticForcingSecondPartial
    (B : Target → Target →L[ℝ] Target →L[ℝ] ℝ)
    (u : Plane → Target) (V : Fin 2 → Plane → Target)
    (W : Fin 2 → Fin 2 → Plane → Target)
    (T : Fin 2 → Fin 2 → Fin 2 → Plane → Target) (a b : Fin 2) : Plane → ℝ :=
  fun z => ∑ i, (fderiv ℝ (fderiv ℝ B) (u z) (V b z) (V a z) (V i z) (V i z) +
    fderiv ℝ B (u z) (W b a z) (V i z) (V i z) +
    fderiv ℝ B (u z) (V a z) (W b i z) (V i z) +
    fderiv ℝ B (u z) (V a z) (V i z) (W b i z) +
    fderiv ℝ B (u z) (V b z) (W a i z) (V i z) +
    B (u z) (T b a i z) (V i z) + B (u z) (W a i z) (W b i z) +
    fderiv ℝ B (u z) (V b z) (V i z) (W a i z) +
    B (u z) (W b i z) (W a i z) + B (u z) (V i z) (T b a i z))

private theorem bilinear_term_fderiv_apply
    {B : Target → Target →L[ℝ] Target →L[ℝ] ℝ}
    {u v w : Plane → Target} {z : Plane}
    (hB : DifferentiableAt ℝ B (u z)) (hu : DifferentiableAt ℝ u z)
    (hv : DifferentiableAt ℝ v z) (hw : DifferentiableAt ℝ w z) (b : Plane) :
    fderiv ℝ (fun p => B (u p) (v p) (w p)) z b =
      fderiv ℝ B (u z) (fderiv ℝ u z b) (v z) (w z) +
      B (u z) (fderiv ℝ v z b) (w z) + B (u z) (v z) (fderiv ℝ w z b) := by
  have h := ((hB.hasFDerivAt.comp z hu.hasFDerivAt).clm_apply
    hv.hasFDerivAt).clm_apply hw.hasFDerivAt
  simp only [Function.comp_def] at h
  rw [h.fderiv]
  simp only [add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply]
  ring

private theorem trilinear_term_fderiv_apply
    {C : Target → Target →L[ℝ] Target →L[ℝ] Target →L[ℝ] ℝ}
    {u v w t : Plane → Target} {z : Plane}
    (hC : DifferentiableAt ℝ C (u z)) (hu : DifferentiableAt ℝ u z)
    (hv : DifferentiableAt ℝ v z) (hw : DifferentiableAt ℝ w z)
    (ht : DifferentiableAt ℝ t z) (b : Plane) :
    fderiv ℝ (fun p => C (u p) (v p) (w p) (t p)) z b =
      fderiv ℝ C (u z) (fderiv ℝ u z b) (v z) (w z) (t z) +
      C (u z) (fderiv ℝ v z b) (w z) (t z) +
      C (u z) (v z) (fderiv ℝ w z b) (t z) +
      C (u z) (v z) (w z) (fderiv ℝ t z b) := by
  have h := (((hC.hasFDerivAt.comp z hu.hasFDerivAt).clm_apply
    hv.hasFDerivAt).clm_apply hw.hasFDerivAt).clm_apply ht.hasFDerivAt
  simp only [Function.comp_def] at h
  rw [h.fderiv]
  simp only [add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply]
  ring





theorem quadraticForcingPartial_fderiv_apply
    {B : Target → Target →L[ℝ] Target →L[ℝ] ℝ}
    {u : Plane → Target} {V : Fin 2 → Plane → Target}
    {W : Fin 2 → Fin 2 → Plane → Target}
    {T : Fin 2 → Fin 2 → Fin 2 → Plane → Target} {z : Plane} (a b : Fin 2)
    (hB : DifferentiableAt ℝ B (u z)) (hDB : DifferentiableAt ℝ (fderiv ℝ B) (u z))
    (hu : DifferentiableAt ℝ u z) (hV : ∀ i, DifferentiableAt ℝ (V i) z)
    (hW : ∀ i, DifferentiableAt ℝ (W a i) z)
    (hdu : fderiv ℝ u z (EuclideanSpace.single b 1) = V b z)
    (hdV : ∀ i, fderiv ℝ (V i) z (EuclideanSpace.single b 1) = W b i z)
    (hdW : ∀ i, fderiv ℝ (W a i) z (EuclideanSpace.single b 1) = T b a i z) :
    fderiv ℝ (quadraticForcingPartial B u V W a) z (EuclideanSpace.single b 1) =
      quadraticForcingSecondPartial B u V W T a b z := by
  have h0 (i : Fin 2) : DifferentiableAt ℝ
      (fun p => fderiv ℝ B (u p) (V a p) (V i p) (V i p)) z :=
    (((hDB.comp z hu).clm_apply (hV a)).clm_apply (hV i)).clm_apply (hV i)
  have h1 (i : Fin 2) : DifferentiableAt ℝ
      (fun p => B (u p) (W a i p) (V i p)) z :=
    ((hB.comp z hu).clm_apply (hW i)).clm_apply (hV i)
  have h2 (i : Fin 2) : DifferentiableAt ℝ
      (fun p => B (u p) (V i p) (W a i p)) z :=
    ((hB.comp z hu).clm_apply (hV i)).clm_apply (hW i)
  have h01 (i : Fin 2) : DifferentiableAt ℝ (fun p =>
      fderiv ℝ B (u p) (V a p) (V i p) (V i p) + B (u p) (W a i p) (V i p)) z :=
    (h0 i).add (h1 i)
  have hd (i : Fin 2) : DifferentiableAt ℝ (fun p =>
      fderiv ℝ B (u p) (V a p) (V i p) (V i p) +
        B (u p) (W a i p) (V i p) + B (u p) (V i p) (W a i p)) z :=
    (h01 i).add (h2 i)
  change fderiv ℝ (fun p : Plane => ∑ i : Fin 2,
    (fderiv ℝ B (u p) (V a p) (V i p) (V i p) +
      B (u p) (W a i p) (V i p) + B (u p) (V i p) (W a i p))) z
        (EuclideanSpace.single b 1) = _
  rw [fderiv_fun_sum (fun i _ => hd i)]
  simp only [sum_apply, quadraticForcingSecondPartial]
  apply Finset.sum_congr rfl
  intro i _
  rw [fderiv_fun_add (h01 i) (h2 i), fderiv_fun_add (h0 i) (h1 i)]
  simp only [add_apply]
  rw [trilinear_term_fderiv_apply hDB hu (hV a) (hV i) (hV i),
    bilinear_term_fderiv_apply hB hu (hW i) (hV i),
    bilinear_term_fderiv_apply hB hu (hV i) (hW i), hdu, hdV a, hdV i, hdW i]
  ring

private theorem eval_memLp
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {mu : Measure Plane} {p q r : ℝ≥0∞} [ENNReal.HolderTriple p q r]
    {A : Plane → E →L[ℝ] F} {v : Plane → E}
    (hA : MemLp A q mu) (hv : MemLp v p mu) : MemLp (fun z => A z (v z)) r mu :=
  (ContinuousLinearMap.apply ℝ F («E» := E)).memLp_of_bilin r hv hA

private theorem quadratic_second_memLp
    {B : Target → Target →L[ℝ] Target →L[ℝ] ℝ}
    {u : Plane → Target} {V : Fin 2 → Plane → Target}
    {W : Fin 2 → Fin 2 → Plane → Target}
    {T : Fin 2 → Fin 2 → Fin 2 → Plane → Target} {mu : Measure Plane}
    [IsFiniteMeasure mu]
    (hB : MemLp (fun z => B (u z)) ⊤ mu)
    (hDB : MemLp (fun z => fderiv ℝ B (u z)) ⊤ mu)
    (hDDB : MemLp (fun z => fderiv ℝ (fderiv ℝ B) (u z)) ⊤ mu)
    (hV : ∀ i, MemLp (V i) ⊤ mu) (hW : ∀ a i, MemLp (W a i) 4 mu)
    (hT : ∀ b a i, MemLp (T b a i) 2 mu) (a b : Fin 2) :
    MemLp (quadraticForcingSecondPartial B u V W T a b) 2 mu := by
  let : ENNReal.HolderTriple 4 4 2 := ENNReal.HolderTriple.of_toReal
    ⟨by norm_num, by norm_num, by norm_num⟩
  have hW2 (j i : Fin 2) : MemLp (W j i) 2 mu :=
    (hW j i).mono_exponent (by norm_num)
  apply memLp_finsetSum
  intro i _
  have h0 : MemLp (fun z =>
      fderiv ℝ (fderiv ℝ B) (u z) (V b z) (V a z) (V i z) (V i z)) ⊤ mu :=
    eval_memLp (r := ⊤) (eval_memLp (r := ⊤) (eval_memLp (r := ⊤)
      (eval_memLp (r := ⊤) hDDB (hV b)) (hV a)) (hV i)) (hV i)
  have h1 : MemLp (fun z => fderiv ℝ B (u z) (W b a z) (V i z) (V i z)) 2 mu :=
    eval_memLp (r := 2) (eval_memLp (r := 2)
      (eval_memLp (r := 2) hDB (hW2 b a)) (hV i)) (hV i)
  have h2 : MemLp (fun z => fderiv ℝ B (u z) (V a z) (W b i z) (V i z)) 2 mu :=
    eval_memLp (r := 2) (eval_memLp (r := 2)
      (eval_memLp (r := ⊤) hDB (hV a)) (hW2 b i)) (hV i)
  have h3 : MemLp (fun z => fderiv ℝ B (u z) (V a z) (V i z) (W b i z)) 2 mu :=
    eval_memLp (r := 2) (eval_memLp (r := ⊤)
      (eval_memLp (r := ⊤) hDB (hV a)) (hV i)) (hW2 b i)
  have h4 : MemLp (fun z => fderiv ℝ B (u z) (V b z) (W a i z) (V i z)) 2 mu :=
    eval_memLp (r := 2) (eval_memLp (r := 2)
      (eval_memLp (r := ⊤) hDB (hV b)) (hW2 a i)) (hV i)
  have h5 : MemLp (fun z => B (u z) (T b a i z) (V i z)) 2 mu :=
    eval_memLp (r := 2) (eval_memLp (r := 2) hB (hT b a i)) (hV i)
  have h6 : MemLp (fun z => B (u z) (W a i z) (W b i z)) 2 mu :=
    eval_memLp (r := 2) (eval_memLp (r := 4) hB (hW a i)) (hW b i)
  have h7 : MemLp (fun z => fderiv ℝ B (u z) (V b z) (V i z) (W a i z)) 2 mu :=
    eval_memLp (r := 2) (eval_memLp (r := ⊤)
      (eval_memLp (r := ⊤) hDB (hV b)) (hV i)) (hW2 a i)
  have h8 : MemLp (fun z => B (u z) (W b i z) (W a i z)) 2 mu :=
    eval_memLp (r := 2) (eval_memLp (r := 4) hB (hW b i)) (hW a i)
  have h9 : MemLp (fun z => B (u z) (V i z) (T b a i z)) 2 mu :=
    eval_memLp (r := 2) (eval_memLp (r := ⊤) hB (hV i)) (hT b a i)
  exact (((((((((h0.mono_exponent le_top).add h1).add h2).add h3).add h4).add h5
    ).add h6).add h7).add h8).add h9

private theorem weak_partial_of_contDiffOn_eq
    {U : Set Plane} (hU : IsOpen U) {f g : Plane → ℝ}
    (hf : ContDiffOn ℝ 1 f U) (a : Fin 2)
    (hg : ∀ z ∈ U, fderiv ℝ f z (EuclideanSpace.single a 1) = g z) :
    HasWeakPartialDeriv a g f U := by
  intro phi hp hc hs
  have h := setIntegral_test_fderiv hU hf hp hc hs (EuclideanSpace.single a 1)
  have heq : (∫ z in U, phi z * fderiv ℝ f z (EuclideanSpace.single a 1)) =
      ∫ z in U, g z * phi z := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem hU.measurableSet] with z hz
    rw [hg z hz, mul_comm]
  simp only [smul_eq_mul] at h
  rw [heq] at h
  simp only [mul_comm (fderiv ℝ phi _ _)] at h
  linarith







theorem quadraticForcing_memWkp_two
    {U : Set Plane} {O : Set Target} (hU : IsOpen U)
    (hfinite : volume U < ⊤) (hO : IsOpen O)
    {B : Target → Target →L[ℝ] Target →L[ℝ] ℝ}
    {u : Plane → Target} {V : Fin 2 → Plane → Target}
    {W : Fin 2 → Fin 2 → Plane → Target}
    {T : Fin 2 → Fin 2 → Fin 2 → Plane → Target}
    (hB : ContDiffOn ℝ 2 B O) (hu : ContDiffOn ℝ 1 u U)
    (hV : ∀ i, ContDiffOn ℝ 1 (V i) U)
    (hW : ∀ a i, ContDiffOn ℝ 1 (W a i) U) (huO : MapsTo u U O)
    (hdu : ∀ a z, z ∈ U → fderiv ℝ u z (EuclideanSpace.single a 1) = V a z)
    (hdV : ∀ a i z, z ∈ U →
      fderiv ℝ (V i) z (EuclideanSpace.single a 1) = W a i z)
    (hdW : ∀ b a i z, z ∈ U →
      fderiv ℝ (W a i) z (EuclideanSpace.single b 1) = T b a i z)
    {C0 C1 C2 A : ℝ} (hBb : ∀ z ∈ U, ‖B (u z)‖ ≤ C0)
    (hDBb : ∀ z ∈ U, ‖fderiv ℝ B (u z)‖ ≤ C1)
    (hDDBb : ∀ z ∈ U, ‖fderiv ℝ (fderiv ℝ B) (u z)‖ ≤ C2)
    (hVb : ∀ i z, z ∈ U → ‖V i z‖ ≤ A)
    (hWLp : ∀ a i, MemLp (W a i) 4 (volume.restrict U))
    (hTLp : ∀ b a i, MemLp (T b a i) 2 (volume.restrict U)) :
    MemWkp 2 2 (quadraticForcing B u V) U := by
  let : IsFiniteMeasure (volume.restrict U) := isFiniteMeasure_restrict.mpr hfinite.ne
  have hB1 : ContDiffOn ℝ 1 B O := hB.of_le (by norm_num)
  have hDB : ContDiffOn ℝ 1 (fderiv ℝ B) O := hB.fderiv_of_isOpen hO (by norm_num)
  have hW2 (a i : Fin 2) : MemLp (W a i) 2 (volume.restrict U) :=
    (hWLp a i).mono_exponent (by norm_num)
  obtain ⟨hF, hFp⟩ := quadraticForcing_memWkp_one hU hfinite hO hB1 hu hV huO
    hdu hdV hBb hDBb hVb hW2
  have hBc := hB1.continuousOn.comp hu.continuousOn huO
  have hDBc := hDB.continuousOn.comp hu.continuousOn huO
  have hDDBc := (hDB.continuousOn_fderiv_of_isOpen hO le_rfl).comp hu.continuousOn huO
  have hBM : MemLp (fun z => B (u z)) ⊤ (volume.restrict U) :=
    memLp_top_of_bound (hBc.aestronglyMeasurable hU.measurableSet) C0 (by
      filter_upwards [ae_restrict_mem hU.measurableSet] with z hz
      exact hBb z hz)
  have hDBM : MemLp (fun z => fderiv ℝ B (u z)) ⊤ (volume.restrict U) :=
    memLp_top_of_bound (hDBc.aestronglyMeasurable hU.measurableSet) C1 (by
      filter_upwards [ae_restrict_mem hU.measurableSet] with z hz
      exact hDBb z hz)
  have hDDBM : MemLp (fun z => fderiv ℝ (fderiv ℝ B) (u z)) ⊤ (volume.restrict U) :=
    memLp_top_of_bound (hDDBc.aestronglyMeasurable hU.measurableSet) C2 (by
      filter_upwards [ae_restrict_mem hU.measurableSet] with z hz
      exact hDDBb z hz)
  have hVM (i : Fin 2) : MemLp (V i) ⊤ (volume.restrict U) :=
    memLp_top_of_bound ((hV i).continuousOn.aestronglyMeasurable hU.measurableSet) A (by
      filter_upwards [ae_restrict_mem hU.measurableSet] with z hz
      exact hVb i z hz)
  have hDDM (a b : Fin 2) := quadratic_second_memLp hBM hDBM hDDBM hVM hWLp hTLp a b
  have hFs (a : Fin 2) : ContDiffOn ℝ 1 (quadraticForcingPartial B u V W a) U :=
    ContDiffOn.sum (fun i _ =>
      (((((hDB.comp hu huO).clm_apply (hV a)).clm_apply (hV i)).clm_apply (hV i)).add
        (((hB1.comp hu huO).clm_apply (hW a i)).clm_apply (hV i))).add
          (((hB1.comp hu huO).clm_apply (hV i)).clm_apply (hW a i)))
  have hw (a b : Fin 2) : HasWeakPartialDeriv b
      (quadraticForcingSecondPartial B u V W T a b) (quadraticForcingPartial B u V W a) U := by
    apply weak_partial_of_contDiffOn_eq hU (hFs a) b
    intro z hz
    exact quadraticForcingPartial_fderiv_apply a b
      ((hB1.contDiffAt (hO.mem_nhds (huO hz))).differentiableAt one_ne_zero)
      ((hDB.contDiffAt (hO.mem_nhds (huO hz))).differentiableAt one_ne_zero)
      ((hu.contDiffAt (hU.mem_nhds hz)).differentiableAt one_ne_zero)
      (fun i => ((hV i).contDiffAt (hU.mem_nhds hz)).differentiableAt one_ne_zero)
      (fun i => ((hW a i).contDiffAt (hU.mem_nhds hz)).differentiableAt one_ne_zero)
      (hdu b z hz) (fun i => hdV b i z hz) (fun i => hdW b a i z hz)
  refine ⟨hF.memW1p, fun a => ?_⟩
  have hp : chosenWeakPartial' 2 a (quadraticForcing B u V) U
      =ᵐ[volume.restrict U] quadraticForcingPartial B u V W a :=
    HasWeakPartialDeriv.ae_eq hU
      (chosenWeakPartial'_isWeakPartial_of_mem hF.memW1p a) (hFp a).2
      ((chosenWeakPartial'_memLp_of_mem hF.memW1p a).locallyIntegrable (by norm_num))
      ((hFp a).1.locallyIntegrable (by norm_num))
  apply (MemWkp_congr_ae (by norm_num) hU hp).mpr
  apply MemWkp.one_iff_memW1p.mpr
  exact ⟨(hFp a).1, fun b => ⟨quadraticForcingSecondPartial B u V W T a b, hDDM a b, hw a b⟩⟩

end PoincareConjecture.M64.RampTransport
