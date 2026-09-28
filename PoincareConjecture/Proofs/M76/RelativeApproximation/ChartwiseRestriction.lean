import PoincareConjecture.Proofs.M76.Triangulation.HamiltonPLDomainComposition










set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76

variable {X Y ι κ : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  {R : Set X} {T : Set Y} {U V : Set R}




theorem ChartwisePLOn.congr_mono
    {e : ι → OpenPartialHomeomorph X (Fin 3 → ℝ)}
    {d : κ → OpenPartialHomeomorph Y (Fin 3 → ℝ)}
    {f g : C(R, T)} (hf : ChartwisePLOn e d f U)
    (hV : IsOpen V) (hVU : V ⊆ U) (hfg : EqOn f g V) :
    ChartwisePLOn e d g V := by
  classical
  refine ⟨hf.source_domain, hf.target_domain, hV, ?_⟩
  intro x hx
  obtain ⟨i, j, K, W, F, hK, hW, hxW, _, hWi, hWK, hKt, hKU, hF, hFval⟩ :=
    hf.coordinates x (hVU hx)
  let q : (Fin 3 → ℝ) → R := fun z =>
    if hz : (e i).symm z ∈ R then ⟨(e i).symm z, hz⟩ else x
  have hqval (z : Fin 3 → ℝ) (hz : z ∈ K.space) : (q z : X) = (e i).symm z := by
    obtain ⟨y, _, hy⟩ := hKU hz
    have hzR : (e i).symm z ∈ R := hy ▸ y.property
    simp only [q, dif_pos hzR]
  have hqi (z : Fin 3 → ℝ) (hz : z ∈ K.space) : (q z : X) ∈ (e i).source := by
    rw [hqval z hz]
    exact (e i).map_target (hKt hz)
  have heq (z : Fin 3 → ℝ) (hz : z ∈ K.space) : e i (q z) = z := by
    rw [hqval z hz, (e i).right_inv (hKt hz)]
  have hqinv (y : R) (hy : (y : X) ∈ (e i).source)
      (hyK : e i y ∈ K.space) : q (e i y) = y := by
    apply Subtype.ext
    rw [hqval _ hyK, (e i).left_inv hy]
  have hqc : ContinuousOn q K.space :=
    Topology.IsEmbedding.subtypeVal.continuousOn_iff.mpr
      (((e i).symm.continuousOn.mono hKt).congr hqval)
  have hxK : e i x ∈ K.space := hWK (mem_image_of_mem _ hxW)
  let xK : K.space := ⟨e i x, hxK⟩
  let O : Set K.space := (fun z => q z) ⁻¹' V
  have hO : IsOpen O := hV.preimage
    (hqc.comp_continuous continuous_subtype_val (fun z => z.property))
  have hxO : xK ∈ O := by
    change q (e i x) ∈ V
    rwa [hqinv x (hWi hxW) hxK]
  obtain ⟨N, V', hN, hNK, hV', hxV', hV'N, hNO⟩ :=
    K.exists_relative_polyhedral_neighborhood hK xK hO hxO
  have hqV (z : Fin 3 → ℝ) (hz : z ∈ N.space) : q z ∈ V :=
    hNO (show (⟨z, hNK hz⟩ : K.space) ∈ Subtype.val ⁻¹' N.space from hz)
  obtain ⟨O', hO', hV'O'⟩ := isOpen_induced_iff.mp hV'
  let W' : Set R := W ∩ (fun y : R => e i y) ⁻¹' O'
  have hW' : IsOpen W' :=
    ((e i).continuousOn.comp continuous_subtype_val.continuousOn hWi).isOpen_inter_preimage
      hW hO'
  have hW'N (y : R) (hy : y ∈ W') : e i y ∈ N.space := by
    apply hV'N
    refine ⟨⟨e i y, hWK (mem_image_of_mem _ hy.1)⟩, ?_, rfl⟩
    rw [← hV'O']
    exact hy.2
  refine ⟨i, j, N, W', F, hN, hW', ?_, ?_,
    fun y hy => hWi hy.1, ?_, fun z hz => hKt (hNK hz), ?_,
    hF.restrict N hN hNK, ?_⟩
  · refine ⟨hxW, ?_⟩
    have hx' := hxV'
    rw [← hV'O'] at hx'
    exact hx'
  · intro y hy
    have h := hqV (e i y) (hW'N y hy)
    rwa [hqinv y (hWi hy.1) (hNK (hW'N y hy))] at h
  · rintro z ⟨y, hy, rfl⟩
    exact hW'N y hy
  · intro z hz
    exact ⟨q z, hqV z hz, hqval z (hNK hz)⟩
  · intro y hy hyN
    have hyV : y ∈ V := by
      have h := hqV (e i y) hyN
      rwa [hqinv y hy (hNK hyN)] at h
    simpa only [hfg hyV] using hFval y hy (hNK hyN)

end PoincareConjecture.M76
