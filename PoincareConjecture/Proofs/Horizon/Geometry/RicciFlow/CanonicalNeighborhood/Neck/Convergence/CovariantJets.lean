import PoincareConjecture.Proofs.Horizon.Analysis.Calculus.SmoothCompactness.DomainChange
import PoincareConjecture.Proofs.Horizon.Analysis.Calculus.SmoothCompactness.LinearPostcompose
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.RoundCylinder








set_option autoImplicit false

open Set Filter
open scoped ContDiff Topology BigOperators
open Poincare.Analysis.Calculus

namespace PoincareConjecture

private structure JetConvergence
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (U : Set E) (f : ℕ → E → F) (f₀ : E → F) : Prop where
  smooth : ContDiffOn ℝ ∞ f₀ U
  local_smooth : ∀ x ∈ U, ∃ W, IsOpen W ∧ x ∈ W ∧
    ∀ᶠ i in atTop, ContDiffOn ℝ ∞ (f i) W
  jets : ∀ m K, IsCompact K → K ⊆ U → TendstoUniformlyOn
    (fun i => iteratedFDeriv ℝ m (f i)) (iteratedFDeriv ℝ m f₀) atTop K

namespace JetConvergence

variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  {U : Set E} {f g : ℕ → E → F} {f₀ g₀ : E → F}

private theorem fixed (hU : IsOpen U) {h : E → F}
    (hh : ContDiffOn ℝ ∞ h U) : JetConvergence U (fun _ => h) h := by
  refine ⟨hh, fun x hx => ⟨U, hU, hx, Eventually.of_forall fun _ => hh⟩, ?_⟩
  intro m K hK hKU
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  exact Eventually.of_forall fun _ _ _ => by simpa only [dist_self] using hε

private theorem linear (hU : IsOpen U) (hf : JetConvergence U f f₀)
    (L : F →L[ℝ] G) : JetConvergence U (fun i => L ∘ f i) (L ∘ f₀) := by
  obtain ⟨hl, hj⟩ := smooth_convergence_continuousLinearMap_comp L hU
    hf.smooth hf.local_smooth hf.jets
  exact ⟨hf.smooth.continuousLinearMap_comp L, hl, hj⟩

private theorem sub (hU : IsOpen U) (hf : JetConvergence U f f₀)
    (hg : JetConvergence U g g₀) :
    JetConvergence U (fun i x => f i x - g i x) (fun x => f₀ x - g₀ x) := by
  refine ⟨hf.smooth.sub hg.smooth, ?_, ?_⟩
  · intro x hx
    obtain ⟨V, hV, hxV, hfs⟩ := hf.local_smooth x hx
    obtain ⟨W, hW, hxW, hgs⟩ := hg.local_smooth x hx
    refine ⟨V ∩ W, hV.inter hW, ⟨hxV, hxW⟩, ?_⟩
    filter_upwards [hfs, hgs] with i hfi hgi
    exact (hfi.mono inter_subset_left).sub (hgi.mono inter_subset_right)
  · intro m K hK hKU
    have h := (hf.jets m K hK hKU).sub (hg.jets m K hK hKU)
    apply (h.congr ?_).congr_right ?_
    · filter_upwards [eventually_contDiffAt_on_compact hK hKU hf.local_smooth,
        eventually_contDiffAt_on_compact hK hKU hg.local_smooth] with i hfi hgi x hx
      exact (iteratedFDeriv_sub_apply
        ((hfi x hx).of_le (by exact_mod_cast le_top))
        ((hgi x hx).of_le (by exact_mod_cast le_top))).symm
    · intro x hx
      exact (iteratedFDeriv_sub_apply
        ((hf.smooth.contDiffAt (hU.mem_nhds (hKU hx))).of_le
          (by exact_mod_cast le_top))
        ((hg.smooth.contDiffAt (hU.mem_nhds (hKU hx))).of_le
          (by exact_mod_cast le_top))).symm

private theorem add (hU : IsOpen U) (hf : JetConvergence U f f₀)
    (hg : JetConvergence U g g₀) :
    JetConvergence U (fun i x => f i x + g i x) (fun x => f₀ x + g₀ x) := by
  simpa using hf.sub hU (hg.linear hU (-ContinuousLinearMap.id ℝ F))

private theorem sum {ι : Type*} (hU : IsOpen U) (s : Finset ι)
    {f : ι → ℕ → E → F} {f₀ : ι → E → F}
    (hf : ∀ a ∈ s, JetConvergence U (f a) (f₀ a)) :
    JetConvergence U (fun i x => ∑ a ∈ s, f a i x) (fun x => ∑ a ∈ s, f₀ a x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using fixed hU (contDiffOn_const (c := (0 : F)))
  | @insert a s ha ih =>
    simpa only [Finset.sum_insert ha] using
      (hf a (Finset.mem_insert_self a s)).add hU
        (ih (fun b hb => hf b (Finset.mem_insert_of_mem hb)))

private theorem directional (hU : IsOpen U) (hf : JetConvergence U f f₀) (v : E) :
    JetConvergence U (fun i x => fderiv ℝ (f i) x v)
      (fun x => fderiv ℝ f₀ x v) := by
  have hd : JetConvergence U (fun i => fderiv ℝ (f i)) (fderiv ℝ f₀) := by
    refine ⟨hf.smooth.fderiv_of_isOpen hU (by simp), ?_, ?_⟩
    · intro x hx
      obtain ⟨W, hW, hxW, hws⟩ := hf.local_smooth x hx
      exact ⟨W, hW, hxW, hws.mono fun i hi => hi.fderiv_of_isOpen hW (by simp)⟩
    · intro m K hK hKU
      exact tendstoUniformlyOn_fderiv_jets m (hf.jets (m + 1) K hK hKU)
  exact hd.linear hU (ContinuousLinearMap.apply ℝ F v)

private theorem mul [FiniteDimensional ℝ E]
    {f g : ℕ → E → ℝ} {f₀ g₀ : E → ℝ}
    (hU : IsOpen U) (hf : JetConvergence U f f₀) (hg : JetConvergence U g g₀) :
    JetConvergence U (fun i x => f i x * g i x) (fun x => f₀ x * g₀ x) := by
  obtain ⟨hl, hj⟩ := smooth_convergence_bilinear_on_finiteDimensional hU
    (ContinuousLinearMap.mul ℝ ℝ) hf.smooth hg.smooth
    hf.local_smooth hg.local_smooth hf.jets hg.jets
  exact ⟨hf.smooth.mul hg.smooth,
    fun x hx => let ⟨W, hW, hxW, _, hws⟩ := hl x hx; ⟨W, hW, hxW, hws⟩, hj⟩

end JetConvergence

private theorem roundCylinderTensorDerivative_convergence
    (u : ℝ)
    (c : OpenPartialHomeomorph UnitTwoSphere (EuclideanSpace ℝ (Fin 2)))
    (cseq : ℕ → OpenPartialHomeomorph UnitTwoSphere (EuclideanSpace ℝ (Fin 2)))
    (hChristoffelEq : ∀ i, roundCylinderChristoffel u (cseq i) =
      roundCylinderChristoffel u c)
    {U : Set RoundCylinderCoordinates} (hU : IsOpen U)
    (hChristoffel : ∀ a b d : Fin 3,
      ContDiffOn ℝ ∞ (fun p => roundCylinderChristoffel u c p a b d) U)
    {r : ℕ} {T : ℕ → RoundCylinderCoordinates → (Fin r → Fin 3) → ℝ}
    (hT : ∀ a, JetConvergence U (fun i p => T i p a) (fun _ => 0))
    (a : Fin (r + 1) → Fin 3) :
    JetConvergence U (fun i p => roundCylinderTensorDerivative u (cseq i) (T i) p a)
      (fun _ => 0) := by
  have hd := (hT (fun i => a i.succ)).directional hU (roundCylinderCoordinateBasis (a 0))
  have hs := JetConvergence.sum hU Finset.univ (fun i _ =>
    JetConvergence.sum hU Finset.univ (fun j _ =>
      (JetConvergence.fixed hU (hChristoffel j (a 0) (a i.succ))).mul hU
        (hT (Function.update (fun k => a k.succ) i j))))
  simpa [roundCylinderTensorDerivative, hChristoffelEq] using hd.sub hU hs



theorem roundCylinderIteratedDerivative_smooth_convergence
    (u : ℝ)
    (c : OpenPartialHomeomorph UnitTwoSphere (EuclideanSpace ℝ (Fin 2)))
    {U : Set RoundCylinderCoordinates} (hU : IsOpen U)
    (hChristoffel : ∀ a b d : Fin 3,
      ContDiffOn ℝ ∞ (fun p => roundCylinderChristoffel u c p a b d) U)
    (hGram : ∀ a b : Fin 3,
      ContDiffOn ℝ ∞ (fun p => roundCylinderGram u c p a b) U)
    {B : ℕ → RoundCylinderTwoTensor}
    (hlocal : ∀ a b : Fin 3, ∀ p ∈ U, ∃ W : Set RoundCylinderCoordinates,
      IsOpen W ∧ p ∈ W ∧ ∀ᶠ i in atTop,
        ContDiffOn ℝ ∞ (fun q => roundCylinderTensorCoefficient (B i) c q a b) W)
    (hjet : ∀ a b : Fin 3, ∀ m : ℕ, ∀ K : Set RoundCylinderCoordinates,
      IsCompact K → K ⊆ U → TendstoUniformlyOn
        (fun i => iteratedFDeriv ℝ m
          (fun p => roundCylinderTensorCoefficient (B i) c p a b))
        (iteratedFDeriv ℝ m (fun p => roundCylinderGram u c p a b)) atTop K) :
    ∀ (k : ℕ) (a : Fin (2 + k) → Fin 3),
      (∀ p ∈ U, ∃ W : Set RoundCylinderCoordinates, IsOpen W ∧ p ∈ W ∧
        ∀ᶠ i in atTop, ContDiffOn ℝ ∞
          (fun q => roundCylinderIteratedDerivative u c (B i) k q a) W) ∧
      ∀ (m : ℕ) (K : Set RoundCylinderCoordinates), IsCompact K → K ⊆ U →
        TendstoUniformlyOn
          (fun i => iteratedFDeriv ℝ m
            (fun p => roundCylinderIteratedDerivative u c (B i) k p a))
          (fun _ => 0) atTop K := by
  have h (k : ℕ) (a : Fin (2 + k) → Fin 3) :
      JetConvergence U (fun i p => roundCylinderIteratedDerivative u c (B i) k p a)
        (fun _ => 0) := by
    induction k with
    | zero =>
      have hc : JetConvergence U
          (fun i p => roundCylinderTensorCoefficient (B i) c p (a 0) (a 1))
          (fun p => roundCylinderGram u c p (a 0) (a 1)) :=
        ⟨hGram (a 0) (a 1), hlocal (a 0) (a 1), hjet (a 0) (a 1)⟩
      simpa [roundCylinderIteratedDerivative] using
        hc.sub hU (JetConvergence.fixed hU (hGram (a 0) (a 1)))
    | succ k ih =>
      exact roundCylinderTensorDerivative_convergence u c (fun _ => c)
        (fun _ => rfl) hU hChristoffel ih a
  intro k a
  refine ⟨(h k a).local_smooth, ?_⟩
  intro m K hK hKU
  exact ((h k a).jets m K hK hKU).congr_right (fun _ _ => by simp)



theorem tendstoUniformlyOn_roundCylinderIteratedDerivative
    (u : ℝ)
    (c : OpenPartialHomeomorph UnitTwoSphere (EuclideanSpace ℝ (Fin 2)))
    {U : Set RoundCylinderCoordinates} (hU : IsOpen U)
    (hChristoffel : ∀ a b d : Fin 3,
      ContDiffOn ℝ ∞ (fun p => roundCylinderChristoffel u c p a b d) U)
    (hGram : ∀ a b : Fin 3,
      ContDiffOn ℝ ∞ (fun p => roundCylinderGram u c p a b) U)
    {B : ℕ → RoundCylinderTwoTensor}
    (hlocal : ∀ a b : Fin 3, ∀ p ∈ U, ∃ W : Set RoundCylinderCoordinates,
      IsOpen W ∧ p ∈ W ∧ ∀ᶠ i in atTop,
        ContDiffOn ℝ ∞ (fun q => roundCylinderTensorCoefficient (B i) c q a b) W)
    (hjet : ∀ a b : Fin 3, ∀ m : ℕ, ∀ K : Set RoundCylinderCoordinates,
      IsCompact K → K ⊆ U → TendstoUniformlyOn
        (fun i => iteratedFDeriv ℝ m
          (fun p => roundCylinderTensorCoefficient (B i) c p a b))
        (iteratedFDeriv ℝ m (fun p => roundCylinderGram u c p a b)) atTop K)
    (k : ℕ) (a : Fin (2 + k) → Fin 3)
    {K : Set RoundCylinderCoordinates} (hK : IsCompact K) (hKU : K ⊆ U) :
    TendstoUniformlyOn
      (fun i p => roundCylinderIteratedDerivative u c (B i) k p a)
      (fun _ => 0) atTop K := by
  have h := (roundCylinderIteratedDerivative_smooth_convergence u c hU
    hChristoffel hGram hlocal hjet k a).2 0 K hK hKU
  simpa only [Function.comp_def, iteratedFDeriv_zero_apply,
    zero_apply] using
    (ContinuousMultilinearMap.uniformContinuous_eval_const
      (0 : Fin 0 → RoundCylinderCoordinates)).comp_tendstoUniformlyOn h



theorem roundCylinderIteratedDerivative_smooth_convergence_of_changing_charts
    (u : ℝ)
    (c : OpenPartialHomeomorph UnitTwoSphere (EuclideanSpace ℝ (Fin 2)))
    (cseq : ℕ → OpenPartialHomeomorph UnitTwoSphere (EuclideanSpace ℝ (Fin 2)))
    (hGramEq : ∀ i, roundCylinderGram u (cseq i) = roundCylinderGram u c)
    (hChristoffelEq : ∀ i, roundCylinderChristoffel u (cseq i) =
      roundCylinderChristoffel u c)
    {U : Set RoundCylinderCoordinates} (hU : IsOpen U)
    (hChristoffel : ∀ a b d : Fin 3,
      ContDiffOn ℝ ∞ (fun p => roundCylinderChristoffel u c p a b d) U)
    (hGram : ∀ a b : Fin 3,
      ContDiffOn ℝ ∞ (fun p => roundCylinderGram u c p a b) U)
    {B : ℕ → RoundCylinderTwoTensor}
    (hlocal : ∀ a b : Fin 3, ∀ p ∈ U, ∃ W : Set RoundCylinderCoordinates,
      IsOpen W ∧ p ∈ W ∧ ∀ᶠ i in atTop,
        ContDiffOn ℝ ∞ (fun q => roundCylinderTensorCoefficient (B i) (cseq i) q a b) W)
    (hjet : ∀ a b : Fin 3, ∀ m : ℕ, ∀ K : Set RoundCylinderCoordinates,
      IsCompact K → K ⊆ U → TendstoUniformlyOn
        (fun i => iteratedFDeriv ℝ m
          (fun p => roundCylinderTensorCoefficient (B i) (cseq i) p a b))
        (iteratedFDeriv ℝ m (fun p => roundCylinderGram u c p a b)) atTop K) :
    ∀ (k : ℕ) (a : Fin (2 + k) → Fin 3),
      (∀ p ∈ U, ∃ W : Set RoundCylinderCoordinates, IsOpen W ∧ p ∈ W ∧
        ∀ᶠ i in atTop, ContDiffOn ℝ ∞
          (fun q => roundCylinderIteratedDerivative u (cseq i) (B i) k q a) W) ∧
      ∀ (m : ℕ) (K : Set RoundCylinderCoordinates), IsCompact K → K ⊆ U →
        TendstoUniformlyOn
          (fun i => iteratedFDeriv ℝ m
            (fun p => roundCylinderIteratedDerivative u (cseq i) (B i) k p a))
          (fun _ => 0) atTop K := by
  have h (k : ℕ) (a : Fin (2 + k) → Fin 3) :
      JetConvergence U (fun i p => roundCylinderIteratedDerivative u (cseq i) (B i) k p a)
        (fun _ => 0) := by
    induction k with
    | zero =>
      have hc : JetConvergence U
          (fun i p => roundCylinderTensorCoefficient (B i) (cseq i) p (a 0) (a 1))
          (fun p => roundCylinderGram u c p (a 0) (a 1)) :=
        ⟨hGram (a 0) (a 1), hlocal (a 0) (a 1), hjet (a 0) (a 1)⟩
      simpa [roundCylinderIteratedDerivative, hGramEq] using
        hc.sub hU (JetConvergence.fixed hU (hGram (a 0) (a 1)))
    | succ k ih =>
      exact roundCylinderTensorDerivative_convergence u c cseq hChristoffelEq
        hU hChristoffel ih a
  intro k a
  refine ⟨(h k a).local_smooth, ?_⟩
  intro m K hK hKU
  exact ((h k a).jets m K hK hKU).congr_right (fun _ _ => by simp)






theorem roundCylinderIteratedDerivative_smooth_zero_convergence_of_changing_charts
    (u : ℝ)
    (c : OpenPartialHomeomorph UnitTwoSphere (EuclideanSpace ℝ (Fin 2)))
    (cseq : ℕ → OpenPartialHomeomorph UnitTwoSphere (EuclideanSpace ℝ (Fin 2)))
    (hChristoffelEq : ∀ i, roundCylinderChristoffel u (cseq i) =
      roundCylinderChristoffel u c)
    {U : Set RoundCylinderCoordinates} (hU : IsOpen U)
    (hChristoffel : ∀ a b d : Fin 3,
      ContDiffOn ℝ ∞ (fun p => roundCylinderChristoffel u c p a b d) U)
    {B : ℕ → RoundCylinderTwoTensor}
    (hlocal : ∀ a b : Fin 3, ∀ p ∈ U, ∃ W : Set RoundCylinderCoordinates,
      IsOpen W ∧ p ∈ W ∧ ∀ᶠ i in atTop,
        ContDiffOn ℝ ∞ (fun q =>
          roundCylinderTensorCoefficient (B i) (cseq i) q a b -
            roundCylinderGram u (cseq i) q a b) W)
    (hjet : ∀ a b : Fin 3, ∀ m : ℕ, ∀ K : Set RoundCylinderCoordinates,
      IsCompact K → K ⊆ U → TendstoUniformlyOn
        (fun i => iteratedFDeriv ℝ m (fun p =>
          roundCylinderTensorCoefficient (B i) (cseq i) p a b -
            roundCylinderGram u (cseq i) p a b))
        (fun _ => 0) atTop K) :
    ∀ (k : ℕ) (a : Fin (2 + k) → Fin 3),
      (∀ p ∈ U, ∃ W : Set RoundCylinderCoordinates, IsOpen W ∧ p ∈ W ∧
        ∀ᶠ i in atTop, ContDiffOn ℝ ∞
          (fun q => roundCylinderIteratedDerivative u (cseq i) (B i) k q a) W) ∧
      ∀ (m : ℕ) (K : Set RoundCylinderCoordinates), IsCompact K → K ⊆ U →
        TendstoUniformlyOn
          (fun i => iteratedFDeriv ℝ m
            (fun p => roundCylinderIteratedDerivative u (cseq i) (B i) k p a))
          (fun _ => 0) atTop K := by
  have h (k : ℕ) (a : Fin (2 + k) → Fin 3) :
      JetConvergence U (fun i p => roundCylinderIteratedDerivative u (cseq i) (B i) k p a)
        (fun _ => 0) := by
    induction k with
    | zero =>
      refine ⟨contDiffOn_const, hlocal (a 0) (a 1), ?_⟩
      intro m K hK hKU
      exact (hjet (a 0) (a 1) m K hK hKU).congr_right (fun _ _ => by simp)
    | succ k ih =>
      exact roundCylinderTensorDerivative_convergence u c cseq hChristoffelEq
        hU hChristoffel ih a
  intro k a
  refine ⟨(h k a).local_smooth, ?_⟩
  intro m K hK hKU
  exact ((h k a).jets m K hK hKU).congr_right (fun _ _ => by simp)

end PoincareConjecture
