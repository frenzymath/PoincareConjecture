import PoincareConjecture.Proofs.M76.Mathlib.ParametricNormalizedExtension
import PoincareConjecture.Proofs.M76.Mathlib.RelativeTransverseGerms










set_option autoImplicit false

open Set ContinuousLinearMap
open scoped Topology ContDiff

variable {X Y E F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [FiniteDimensional ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [FiniteDimensional ℝ Y] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]





theorem Continuous.exists_contDiff_frameTransverse_parametric_coreExtension
    {f : X × Y → E →L[ℝ] F} (hf : Continuous f) (J : F →L[ℝ] E)
    (hframe : ∀ z, Function.RightInverse J (f z)) (n : ℕ∞)
    {C : Set X} (hC : IsCompact C) (hc : Convex ℝ C) (hi : (interior C).Nonempty)
    {P K : Set Y} (hP : IsCompact P) (hK : IsCompact K) (hKP : K ⊆ interior P)
    {S V : Set (X × Y)} (hS : IsClosed S) (hSC : S ⊆ (interior C)ᶜ ×ˢ K)
    (hV : V ∈ 𝓝ˢ S) (hfV : ContDiffOn ℝ n f V) (A : Set E)
    [ContractibleSpace {Q : E →L[ℝ] F // Function.RightInverse J Q ∧
      Q.ker.IsSecantTransverse A}]
    (hfront : ∀ x ∈ frontier C, ∀ p ∈ P, (f (x, p)).ker.IsSecantTransverse A) :
    ∃ g : X × Y → E →L[ℝ] F, ContDiff ℝ n g ∧
      (∀ z, Function.RightInverse J (g z)) ∧ g =ᶠ[𝓝ˢ S] f ∧
      ∀ z ∈ C ×ˢ K, (g z).ker.IsSecantTransverse A := by
  obtain ⟨g, hgn, heq, hgt⟩ := hf.exists_frameTransverse_parametric_coreExtension
    J hframe hC hc hi hP A hfront
  have heqS : (g : X × Y → E →L[ℝ] F) =ᶠ[𝓝ˢ S] f :=
    heq.filter_mono (nhdsSet_mono (hSC.trans (prod_mono Subset.rfl hKP)))
  obtain ⟨O, hO, hSO, hOeq⟩ := eventually_nhdsSet_iff_exists.mp heqS
  have hVO : V ∩ O ∈ 𝓝ˢ S := Filter.inter_mem hV (hO.mem_nhdsSet.mpr hSO)
  have hgsmooth : ContDiffOn ℝ n (g : X × Y → E →L[ℝ] F) (V ∩ O) :=
    (hfV.mono inter_subset_left).congr (fun z hz => hOeq z hz.2)
  obtain ⟨k, hk, hkn, hkeq, hkt⟩ :=
    g.continuous.exists_contDiff_frameTransverse_eventuallyEq J hgn n
      (hC.prod hK) hS hVO hgsmooth A
      (fun z hz => hgt z ⟨hz.1, interior_subset (hKP hz.2)⟩)
  exact ⟨k, hk, hkn, hkeq.trans heqS, hkt⟩
