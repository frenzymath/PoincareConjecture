import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Collars.Mathlib.CollarInteriorLoops








set_option autoImplicit false
open Set

namespace Poincare.Topology

theorem exists_phase_rim_collar
    {E X Y : Type*} [TopologicalSpace E] [TopologicalSpace X] [T2Space X]
    [TopologicalSpace Y] [T2Space Y]
    {K : Set E} (hK : IsCompact K) {r : ℝ} (hr : 0 < r)
    (c : E × ℝ → X)
    (hc : ContinuousOn c (K ×ˢ Icc (-r) r))
    (hi : Topology.IsEmbedding (fun z : (K ×ˢ Icc (-r) r : Set (E × ℝ)) => c z))
    (ho : IsOpen (c '' (K ×ˢ Ioo (-r) r)))
    {R : Set X} (hzero : c '' (K ×ˢ ({0} : Set ℝ)) = frontier R)
    (hside : ∀ z ∈ K ×ˢ Icc (-r) r, c z ∈ R ↔ 0 ≤ z.2)
    (q : C(X, Y)) (hphase : ∀ z ∈ K ×ˢ Icc (-r) r, q (c z) = q (c (z.1, 0)))
    (theta : Y) (x0 : ↥(R ∩ q ⁻¹' {theta})) :
    let Ktheta := K ∩ (fun z => q (c (z, 0))) ⁻¹' {theta}
    let S := R ∩ q ⁻¹' {theta}
    IsCompact Ktheta ∧ ∃ cS : E × ℝ → S,
      (∀ z ∈ Ktheta ×ˢ Icc (0 : ℝ) r, (cS z : X) = c z) ∧
      ContinuousOn cS (Ktheta ×ˢ Icc (0 : ℝ) r) ∧
      Topology.IsEmbedding (fun z : (Ktheta ×ˢ Icc (0 : ℝ) r : Set (E × ℝ)) => cS z) ∧
      IsOpen (cS '' (Ktheta ×ˢ Ico (0 : ℝ) r)) ∧
      cS '' (Ktheta ×ˢ ({0} : Set ℝ)) = (Subtype.val : S → X) ⁻¹' frontier R := by
  classical
  intro Ktheta S
  have hzero_mem (z : E) (hz : z ∈ K) : (z, (0 : ℝ)) ∈ K ×ˢ Icc (-r) r :=
    ⟨hz, by linarith, hr.le⟩
  have hqc : Continuous (fun z : K => q (c (z, 0))) :=
    q.continuous.comp (hc.comp_continuous
      (continuous_subtype_val.prodMk continuous_const) (fun z => hzero_mem z z.property))
  have hKt : IsCompact Ktheta := by
    let : CompactSpace K := isCompact_iff_compactSpace.mp hK
    have hcompact : IsCompact {z : K | q (c (z, 0)) = theta} :=
      (isClosed_singleton.preimage hqc).isCompact
    have himage : (Subtype.val : K → E) '' {z : K | q (c (z, 0)) = theta} = Ktheta := by
      ext z
      simp only [mem_image, mem_ofPred_eq, Ktheta, mem_inter_iff, mem_preimage, mem_singleton_iff]
      exact ⟨fun ⟨w, hw, heq⟩ => heq ▸ ⟨w.property, hw⟩,
        fun h => ⟨⟨z, h.1⟩, h.2, rfl⟩⟩
    rw [← himage]
    exact hcompact.image continuous_subtype_val
  have hsub : Ktheta ×ˢ Icc (0 : ℝ) r ⊆ K ×ˢ Icc (-r) r := by
    intro z hz
    exact ⟨hz.1.1, by linarith [hz.2.1], hz.2.2⟩
  have hvalid (z : E × ℝ) (hz : z ∈ Ktheta ×ˢ Icc (0 : ℝ) r) : c z ∈ S := by
    exact ⟨(hside z (hsub hz)).mpr hz.2.1, (hphase z (hsub hz)).trans hz.1.2⟩
  let cS : E × ℝ → S := fun z => if h : c z ∈ S then ⟨c z, h⟩ else x0
  have hval (z : E × ℝ) (hz : z ∈ Ktheta ×ˢ Icc (0 : ℝ) r) : (cS z : X) = c z := by
    simp only [cS, dif_pos (hvalid z hz)]
  have hcont : ContinuousOn cS (Ktheta ×ˢ Icc (0 : ℝ) r) := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    have h := (hc.mono hsub).mapsToRestrict hvalid
    convert h using 1
    exact funext (fun z => Subtype.ext (hval z z.property))
  have hemb : Topology.IsEmbedding
      (fun z : (Ktheta ×ˢ Icc (0 : ℝ) r : Set (E × ℝ)) => cS z) := by
    apply Topology.IsEmbedding.of_comp hcont.domRestrict continuous_subtype_val
    convert hi.comp (Topology.IsEmbedding.inclusion hsub) using 1
    exact funext (fun z => hval z z.property)
  have hopen_eq : cS '' (Ktheta ×ˢ Ico (0 : ℝ) r) =
      (Subtype.val : S → X) ⁻¹' (c '' (K ×ˢ Ioo (-r) r)) := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      change (cS z : X) ∈ c '' (K ×ˢ Ioo (-r) r)
      rw [hval z ⟨hz.1, hz.2.1, hz.2.2.le⟩]
      exact ⟨z, ⟨hz.1.1, by linarith [hz.2.1], hz.2.2⟩, rfl⟩
    · rintro ⟨z, hz, hzx⟩
      have hzfull : z ∈ K ×ˢ Icc (-r) r := ⟨hz.1, hz.2.1.le, hz.2.2.le⟩
      have hzpos : 0 ≤ z.2 := (hside z hzfull).mp (hzx.symm ▸ x.property.1)
      have hzphase : q (c (z.1, 0)) = theta := by
        rw [← hphase z hzfull, hzx]
        exact x.property.2
      have hzt : z ∈ Ktheta ×ˢ Ico (0 : ℝ) r := ⟨⟨hz.1, hzphase⟩, hzpos, hz.2.2⟩
      exact ⟨z, hzt, Subtype.ext ((hval z ⟨hzt.1, hzt.2.1, hzt.2.2.le⟩).trans hzx)⟩
  refine ⟨hKt, cS, hval, hcont, hemb, ?_, ?_⟩
  · rw [hopen_eq]
    exact ho.preimage continuous_subtype_val
  · ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      change (cS z : X) ∈ frontier R
      have hzt : z ∈ Ktheta ×ˢ Icc (0 : ℝ) r :=
        ⟨hz.1, by rw [show z.2 = 0 from hz.2]; exact ⟨le_rfl, hr.le⟩⟩
      rw [hval z hzt, ← hzero]
      exact ⟨z, ⟨hz.1.1, hz.2⟩, rfl⟩
    · intro hx
      obtain ⟨z, hz, hzx⟩ := hzero.symm ▸ hx
      have hz0 : z.2 = 0 := hz.2
      have hzfull : z ∈ K ×ˢ Icc (-r) r := ⟨hz.1, by rw [hz0]; exact ⟨by linarith, hr.le⟩⟩
      have hzphase : q (c (z.1, 0)) = theta := by
        rw [← hphase z hzfull, hzx]
        exact x.property.2
      have hzt : z ∈ Ktheta ×ˢ Icc (0 : ℝ) r := ⟨⟨hz.1, hzphase⟩, by rw [hz0]; exact ⟨le_rfl, hr.le⟩⟩
      exact ⟨z, ⟨hzt.1, hz0⟩, Subtype.ext ((hval z hzt).trans hzx)⟩



theorem fundamentalGroup_phase_rim_complement_surjective
    {E X Y : Type*} [TopologicalSpace E] [Zero E]
    [TopologicalSpace X] [T2Space X] [TopologicalSpace Y] [T2Space Y]
    {K : Set E} (hK : IsCompact K) {r : ℝ} (hr : 0 < r)
    (c : E × ℝ → X)
    (hc : ContinuousOn c (K ×ˢ Icc (-r) r))
    (hi : Topology.IsEmbedding (fun z : (K ×ˢ Icc (-r) r : Set (E × ℝ)) => c z))
    (ho : IsOpen (c '' (K ×ˢ Ioo (-r) r)))
    {R : Set X} (hzero : c '' (K ×ˢ ({0} : Set ℝ)) = frontier R)
    (hside : ∀ z ∈ K ×ˢ Icc (-r) r, c z ∈ R ↔ 0 ≤ z.2)
    (q : C(X, Y)) (hphase : ∀ z ∈ K ×ˢ Icc (-r) r, q (c z) = q (c (z.1, 0)))
    (theta : Y) :
    let S := R ∩ q ⁻¹' {theta}
    let B := (Subtype.val : S → X) ⁻¹' frontier R
    ∀ x : ↥Bᶜ, Function.Surjective (FundamentalGroup.map
      (⟨Subtype.val, continuous_subtype_val⟩ : C(↥Bᶜ, S)) x) := by
  intro S B x
  obtain ⟨hKt, cS, _, hcS, hiS, hoS, hzS⟩ :=
    exists_phase_rim_collar hK hr c hc hi ho hzero hside q hphase theta x.val
  have h := fundamentalGroup_collar_rim_complement_surjective hKt hr cS hcS hiS hoS
  rw [hzS] at h
  exact h x

end Poincare.Topology
