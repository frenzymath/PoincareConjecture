import PoincareConjecture.Proofs.M40.Mathlib.SmoothChartDistance
import PoincareConjecture.Proofs.M40.Mathlib.LocalSmoothLipschitz
import PoincareConjecture.Proofs.M40.Mathlib.LipschitzSmoothingFiniteControls
import Mathlib.Topology.Compactness.LocallyCompact












set_option autoImplicit false

open Bundle Set Filter Metric
open scoped Topology Manifold ContDiff NNReal

namespace PoincareConjecture.M40

variable {E F M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [MetricSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [LocallyCompactSpace M]
  [RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _)]
  [IsContinuousRiemannianBundle E (TangentSpace 𝓘(ℝ, E) : M → Type _)]
  [IsRiemannianManifold 𝓘(ℝ, E) M]
  [MetricSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ, F) ∞ N]
  [RiemannianBundle (TangentSpace 𝓘(ℝ, F) : N → Type _)]
  [IsContinuousRiemannianBundle F (TangentSpace 𝓘(ℝ, F) : N → Type _)]
  [IsRiemannianManifold 𝓘(ℝ, F) N]





theorem exists_chart_smoothing_estimate_neighborhood
    (e : OpenPartialHomeomorph M E) (h : OpenPartialHomeomorph N F)
    (he : e.MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ, E))
    (hh : h.MDifferentiable 𝓘(ℝ, F) 𝓘(ℝ, F))
    (hes : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ e e.source)
    (hei : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ e.symm e.target)
    (hhs : ContMDiffOn 𝓘(ℝ, F) 𝓘(ℝ, F) ∞ h h.source)
    (hhi : ContMDiffOn 𝓘(ℝ, F) 𝓘(ℝ, F) ∞ h.symm h.target)
    {f : M → N} (hf : Continuous f)
    {ρ : M → ℝ} (hρ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ ρ)
    {U : Set M} (hU : IsOpen U) (hUe : U ⊆ e.source)
    (hfU : MapsTo f U h.source) {x : M} (hx : x ∈ U)
    {C : ℝ≥0} (hC : 1 < C) :
    ∃ (A : E ≃L[ℝ] TangentSpace 𝓘(ℝ, E) x)
      (B : F ≃L[ℝ] TangentSpace 𝓘(ℝ, F) (f x))
      (V : Set (TangentSpace 𝓘(ℝ, E) x))
      (W : Set (TangentSpace 𝓘(ℝ, F) (f x)))
      (O K : Set M) (D : ℝ≥0),
      IsOpen V ∧ IsOpen W ∧ IsOpen O ∧ IsCompact K ∧
      x ∈ interior K ∧ K ⊆ O ∧ O ⊆ U ∧ 0 < D ∧
      MapsTo A.symm V e.target ∧ MapsTo B.symm W h.target ∧
      MapsTo (fun y => A (e y)) O V ∧
      LipschitzOnWith C (fun y => A (e y)) O ∧
      LipschitzOnWith C (fun v => e.symm (A.symm v)) V ∧
      MapsTo (fun y => B (h (f y))) O W ∧
      LipschitzOnWith C (fun z => B (h z)) (f '' O) ∧
      LipschitzOnWith C (fun v => h.symm (B.symm v)) W ∧
      LipschitzOnWith D ρ O := by
  let ns := normalizedSmoothChart e he (hUe hx)
  let nt := normalizedSmoothChart h hh (hfU hx)
  let A := (chartNormalizationLinearEquiv e he (hUe hx)).symm
  let B := (chartNormalizationLinearEquiv h hh (hfU hx)).symm
  have hxs : x ∈ ns.source := by
    simpa only [ns, normalizedSmoothChart_source] using hUe hx
  have hxt : f x ∈ nt.source := by
    simpa only [nt, normalizedSmoothChart_source] using hfU hx
  obtain ⟨r, hr, hrs, hsInv, hsFwd⟩ :=
    normalizedSmoothChart_exists_lipschitz_ball e he (hUe hx) hes hei C hC
  obtain ⟨s, hs, hst, htInv, htFwd⟩ :=
    normalizedSmoothChart_exists_lipschitz_ball h hh (hfU hx) hhs hhi C hC
  let V := ball (ns x) r
  let W := ball (nt (f x)) s
  have hVtarget : V ⊆ ns.target := hrs
  have hWtarget : W ⊆ nt.target := hst
  have hsourceOpen : IsOpen (ns.symm '' V) :=
    ns.isOpen_image_symm_of_subset_target isOpen_ball hVtarget
  have htargetOpen : IsOpen (nt.symm '' W) :=
    nt.isOpen_image_symm_of_subset_target isOpen_ball hWtarget
  have hxSource : x ∈ ns.symm '' V :=
    ⟨ns x, mem_ball_self hr, ns.left_inv hxs⟩
  have hxTarget : f x ∈ nt.symm '' W :=
    ⟨nt (f x), mem_ball_self hs, nt.left_inv hxt⟩
  obtain ⟨D, hD, Z, hZ, hρZ⟩ :=
    exists_lipschitzOn_nhds_of_contMDiffAt ((hρ x).of_le (by norm_num))
  obtain ⟨Z', hZ'sub, hZ'open, hxZ'⟩ := _root_.mem_nhds_iff.mp hZ
  let O := U ∩ ((ns.symm '' V) ∩ (f ⁻¹' (nt.symm '' W) ∩ Z'))
  have hO : IsOpen O :=
    hU.inter (hsourceOpen.inter ((htargetOpen.preimage hf).inter hZ'open))
  have hxO : x ∈ O := ⟨hx, hxSource, hxTarget, hxZ'⟩
  obtain ⟨K, hK, hxK, hKO⟩ := exists_compact_subset hO hxO
  refine ⟨A, B, V, W, O, K, D, isOpen_ball, isOpen_ball, hO, hK,
    hxK, hKO, fun _ hy => hy.1, hD, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro v hv
    simpa only [ns, normalizedSmoothChart_target, mem_preimage, A,
      ContinuousLinearEquiv.symm_symm] using hVtarget hv
  · intro v hv
    simpa only [nt, normalizedSmoothChart_target, mem_preimage, B,
      ContinuousLinearEquiv.symm_symm] using hWtarget hv
  · rintro y ⟨_, ⟨z, hz, rfl⟩, _⟩
    change ns (ns.symm z) ∈ V
    simpa only [ns.right_inv (hVtarget hz)] using hz
  · exact hsFwd.mono (fun _ hy => hy.2.1)
  · exact hsInv
  · intro y hy
    rcases hy.2.2.1 with ⟨z, hz, hfyz⟩
    change nt (f y) ∈ W
    rw [← hfyz, nt.right_inv (hWtarget hz)]
    exact hz
  · apply htFwd.mono
    rintro z ⟨y, hy, rfl⟩
    exact hy.2.2.1
  · exact htInv
  · exact hρZ.mono (fun _ hy => hZ'sub hy.2.2.2)







theorem exists_finite_chart_smoothing_estimates
    (e : OpenPartialHomeomorph M E) (h : OpenPartialHomeomorph N F)
    (he : e.MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ, E))
    (hh : h.MDifferentiable 𝓘(ℝ, F) 𝓘(ℝ, F))
    (hes : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ e e.source)
    (hei : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ e.symm e.target)
    (hhs : ContMDiffOn 𝓘(ℝ, F) 𝓘(ℝ, F) ∞ h h.source)
    (hhi : ContMDiffOn 𝓘(ℝ, F) 𝓘(ℝ, F) ∞ h.symm h.target)
    {f : M → N} {L : ℝ≥0} (hf : LipschitzWith L f)
    {ρ : M → ℝ} (hρ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ ρ)
    {U S : Set M} (hU : IsOpen U) (hUe : U ⊆ e.source)
    (hfU : MapsTo f U h.source) (hS : IsCompact S) (hSU : S ⊆ U)
    {fext : E → F} (hext : ∀ y ∈ U, fext (e y) = h (f y))
    {C : ℝ≥0} (hC : 1 < C) :
    ∃ s : Finset S,
      ∃ (B : ∀ i : s, F ≃L[ℝ] TangentSpace 𝓘(ℝ, F) (f i.1.1))
        (K : s → Set M)
        (W : ∀ i : s, Set (TangentSpace 𝓘(ℝ, F) (f i.1.1)))
        (D : s → ℝ≥0) (R : ℝ),
        0 < R ∧ (∀ i, IsCompact (K i)) ∧ (∀ i, K i ⊆ U) ∧
        (∀ x ∈ S, ∃ i, x ∈ interior (K i)) ∧
        (∀ i, IsOpen (W i)) ∧ (∀ i, 0 < D i) ∧
        (∀ i, MapsTo (B i).symm (W i) h.target) ∧
        (∀ i, MapsTo (fun x => B i (fext (e x))) (K i) (W i)) ∧
        (∀ i, LipschitzOnWith C (fun v => h.symm ((B i).symm v)) (W i)) ∧
        (∀ i, LipschitzOnWith (D i) ρ (K i)) ∧
        (∀ i, ∀ x ∈ K i, ∀ y ∈ K i, ∀ t ∈ ball (0 : E) R,
          dist (B i (fext (e x - t))) (B i (fext (e y - t))) ≤
            (C * L * (C * C) : ℝ≥0) * dist x y) := by
  classical
  have hlocal (p : S) := exists_chart_smoothing_estimate_neighborhood e h he hh
    hes hei hhs hhi hf.continuous hρ hU hUe hfU (hSU p.2) hC
  choose A B V W O K D hV hW hO hK hpK hKO hOU hD
    hA hB hsourceMap hsourceFwd hsourceInv htargetMap htargetFwd htargetInv hρLip
    using hlocal
  obtain ⟨s, hs⟩ := hS.elim_finite_subcover (fun p : S => interior (K p))
    (fun _ => isOpen_interior) (fun x hx => mem_iUnion.mpr ⟨⟨x, hx⟩, hpK ⟨x, hx⟩⟩)
  obtain ⟨R, hR, hshift⟩ := exists_finite_chart_translation_radius e
    (fun i : s => K i.1) (fun i : s => O i.1) (fun i => hK i.1)
    (fun i => hO i.1) (fun i => hKO i.1) (fun i => (hOU i.1).trans hUe)
  refine ⟨s, (fun i => B i.1), (fun i => K i.1), (fun i => W i.1),
    (fun i => D i.1), R, hR, (fun i => hK i.1),
    (fun i => (hKO i.1).trans (hOU i.1)), ?_, (fun i => hW i.1),
    (fun i => hD i.1), (fun i => hB i.1), ?_, (fun i => htargetInv i.1),
    (fun i => (hρLip i.1).mono (hKO i.1)), ?_⟩
  · intro x hx
    obtain ⟨p, hps, hxp⟩ := mem_iUnion₂.mp (hs hx)
    exact ⟨⟨p, hps⟩, hxp⟩
  · intro i x hx
    change B i.1 (fext (e x)) ∈ W i.1
    rw [hext x (hOU i.1 (hKO i.1 hx))]
    exact htargetMap i.1 (hKO i.1 hx)
  · intro i
    apply chartCoordinates_translated_dist_le e h (B i.1).toContinuousLinearMap
      hf (htargetFwd i.1)
    · intro t ht
      apply chartTranslation_lipschitzOn e (A i.1) t
        ((hsourceFwd i.1).mono (hKO i.1)) (hsourceInv i.1)
      intro x hx
      have hxt := hshift i x hx t ht
      simpa only [e.right_inv hxt.1] using hsourceMap i.1 hxt.2
    · intro x hx t ht
      exact mem_image_of_mem f (hshift i x hx t ht).2
    · intro x hx t ht
      have hxt := hshift i x hx t ht
      simpa only [e.right_inv hxt.1] using hext (e.symm (e x - t)) (hOU i.1 hxt.2)

end PoincareConjecture.M40
