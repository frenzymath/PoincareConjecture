import PoincareConjecture.Proofs.M76.Triangulation.HamiltonProtectedPLDiagram










set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [TopologicalSpace Z] {ι κ ν : Type*}
  {R : Set X} {T : Set Y} {S : Set Z} {U : Set R} {W : Set T}




theorem ChartwisePLOn.comp
    {e : ι → OpenPartialHomeomorph X (Fin 3 → ℝ)}
    {d : κ → OpenPartialHomeomorph Y (Fin 3 → ℝ)}
    {c : ν → OpenPartialHomeomorph Z (Fin 3 → ℝ)}
    {f : C(R, T)} {g : C(T, S)}
    (hg : ChartwisePLOn d c g W) (hf : ChartwisePLOn e d f U) :
    ChartwisePLOn e c (g.comp f) (U ∩ f ⁻¹' W) := by
  classical
  refine ⟨hf.source_domain, hg.target_domain,
    hf.open_domain.inter (hg.open_domain.preimage f.continuous), ?_⟩
  intro x hx
  obtain ⟨i, j, K, V, F, hK, hV, hxV, hVU, hVi, hVK, hKt, hKU, hF, hFval⟩ :=
    hf.coordinates x hx.1
  obtain ⟨j', l, L, Vg, G, _, hVg, hfxVg, hVgW, hVgj, hVgL, _, _, _, hGval⟩ :=
    hg.coordinates (f x) hx.2
  let q : (Fin 3 → ℝ) → R := fun z =>
    if hz : (e i).symm z ∈ R then ⟨(e i).symm z, hz⟩ else x
  have hqval (z : Fin 3 → ℝ) (hz : z ∈ K.space) : (q z : X) = (e i).symm z := by
    obtain ⟨y, _, hy⟩ := hKU hz
    have hzR : (e i).symm z ∈ R := hy ▸ y.property
    simp only [q, dif_pos hzR]
  have hqU (z : Fin 3 → ℝ) (hz : z ∈ K.space) : q z ∈ U := by
    obtain ⟨y, hy, heq⟩ := hKU hz
    have hqy : q z = y := Subtype.ext ((hqval z hz).trans heq.symm)
    rwa [hqy]
  have hqi (z : Fin 3 → ℝ) (hz : z ∈ K.space) : (q z : X) ∈ (e i).source := by
    rw [hqval z hz]
    exact (e i).map_target (hKt hz)
  have heq (z : Fin 3 → ℝ) (hz : z ∈ K.space) : e i (q z) = z := by
    rw [hqval z hz, (e i).right_inv (hKt hz)]
  have hqinv (y : R) (hy : (y : X) ∈ (e i).source)
      (hyK : e i y ∈ K.space) : q (e i y) = y := by
    apply Subtype.ext
    rw [hqval _ hyK, (e i).left_inv hy]
  have hq : ContinuousOn q K.space :=
    Topology.IsEmbedding.subtypeVal.continuousOn_iff.mpr
      (((e i).symm.continuousOn.mono hKt).congr hqval)
  have hxK : e i x ∈ K.space := hVK (mem_image_of_mem _ hxV)
  let xK : K.space := ⟨e i x, hxK⟩
  let O : Set K.space := (fun z => f (q z)) ⁻¹' Vg
  have hO : IsOpen O := hVg.preimage
    (f.continuous.comp (hq.comp_continuous continuous_subtype_val (fun z => z.property)))
  have hxO : xK ∈ O := by
    change f (q (e i x)) ∈ Vg
    rw [hqinv x (hVi hxV) hxK]
    exact hfxVg
  obtain ⟨N, V', hN, hNK, hV', hxV', hV'N, hNO⟩ :=
    K.exists_relative_polyhedral_neighborhood hK xK hO hxO
  have hqfVg (z : Fin 3 → ℝ) (hz : z ∈ N.space) : f (q z) ∈ Vg :=
    hNO (show (⟨z, hNK hz⟩ : K.space) ∈ Subtype.val ⁻¹' N.space from hz)
  have hqf : ContinuousOn (fun z => f (q z)) N.space :=
    (f.continuous.comp_continuousOn hq).mono hNK
  have hqfj (z : Fin 3 → ℝ) (hz : z ∈ N.space) : (f (q z) : Y) ∈ (d j).source :=
    (hFval (q z) (hqi z (hNK hz)) ((heq z (hNK hz)).symm ▸ hNK hz)).1
  have hqfPL : PolyhedralPLInCharts d (fun z => (f (q z) : Y)) N.space := by
    refine ⟨continuous_subtype_val.comp_continuousOn hqf, ?_⟩
    intro z
    refine ⟨j, N, univ, hN, subset_rfl, isOpen_univ, mem_univ _, ?_,
      fun y hy => hqfj y hy, ?_⟩
    · rintro y ⟨z, _, rfl⟩
      exact z.property
    · apply (hF.restrict N hN hNK).congr
      intro y hy
      have h := (hFval (q y) (hqi y (hNK hy))
        ((heq y (hNK hy)).symm ▸ hNK hy)).2
      rwa [heq y (hNK hy)] at h
  have hgimage (z : Fin 3 → ℝ) (hz : z ∈ N.space) :
      (g (f (q z)) : Z) ∈ (c l).source :=
    (hGval (f (q z)) (hVgj (hqfVg z hz))
      (hVgL (mem_image_of_mem _ (hqfVg z hz)))).1
  have hcomposite : FinitePiecewiseAffineOn (fun z => c l (g (f (q z)))) N.space :=
    hg.finitePiecewiseAffineOn_fixed_chart N hN (fun z => f (q z)) hqf hqfPL
      (fun z hz => hVgW (hqfVg z hz)) l hgimage
  obtain ⟨O', hO', hV'O'⟩ := isOpen_induced_iff.mp hV'
  let Vnew : Set R := V ∩ (fun y : R => e i y) ⁻¹' O'
  have hVnew : IsOpen Vnew := by
    have hei : ContinuousOn (fun y : R => e i y) V :=
      (e i).continuousOn.comp continuous_subtype_val.continuousOn hVi
    exact hei.isOpen_inter_preimage hV hO'
  have hVnewN (y : R) (hy : y ∈ Vnew) : e i y ∈ N.space := by
    apply hV'N
    refine ⟨⟨e i y, hVK (mem_image_of_mem _ hy.1)⟩, ?_, rfl⟩
    rw [← hV'O']
    exact hy.2
  refine ⟨i, l, N, Vnew, fun z => c l (g (f (q z))), hN, hVnew, ?_, ?_,
    fun y hy => hVi hy.1, ?_, fun z hz => hKt (hNK hz), ?_, hcomposite, ?_⟩
  · refine ⟨hxV, ?_⟩
    have hx' := hxV'
    rw [← hV'O'] at hx'
    exact hx'
  · intro y hy
    refine ⟨hVU hy.1, ?_⟩
    have h := hVgW (hqfVg (e i y) (hVnewN y hy))
    rwa [hqinv y (hVi hy.1) (hNK (hVnewN y hy))] at h
  · rintro z ⟨y, hy, rfl⟩
    exact hVnewN y hy
  · intro z hz
    exact ⟨q z, ⟨hqU z (hNK hz), hVgW (hqfVg z hz)⟩, hqval z (hNK hz)⟩
  · intro y hy hyN
    have hqy := hqinv y hy (hNK hyN)
    refine ⟨?_, ?_⟩
    · simpa only [ContinuousMap.comp_apply, hqy] using hgimage (e i y) hyN
    · change c l (g (f (q (e i y)))) = c l (g (f y))
      rw [hqy]

end PoincareConjecture.M76
