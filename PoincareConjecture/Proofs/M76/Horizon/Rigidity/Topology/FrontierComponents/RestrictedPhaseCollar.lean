import PoincareConjecture.Proofs.M76.Wall.PLDomainComponents
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.FrontierComponents.ComponentCollar
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.InducedOpenImage

set_option autoImplicit false
open Set Geometry Topology

namespace PoincareConjecture.M76

theorem PLDomain.restrict_phase_collar_to_component
    {E X ι : Type*} [TopologicalSpace E] [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X (Fin 3 → ℝ)} {R F : Set X}
    (he : PLDomain e R) (hR : IsCompact R) {x : X} (hx : x ∈ R)
    (hF : F ⊆ frontier R) {K : Set E} (hK : IsCompact K)
    (c : E × ℝ → X) {r : ℝ} (hr : 0 < r)
    (hi : IsEmbedding (fun z : (K ×ˢ Icc (-r) r : Set (E × ℝ)) => c z))
    (hzero : c '' (K ×ˢ ({0} : Set ℝ)) = F)
    (hside : ∀ z ∈ K ×ˢ Icc (-r) r, c z ∈ R ↔ 0 ≤ z.2)
    (hopen : IsOpen (c '' (K ×ˢ Ioo (-r) r))) :
    let P := _root_.connectedComponentIn R x
    let K' := {z | z ∈ K ∧ c (z, 0) ∈ P}
    IsCompact P ∧ PLDomain e P ∧ IsCompact K' ∧
      IsClopen ((Subtype.val : K → E) ⁻¹' K') ∧
      IsEmbedding (fun z : (K' ×ˢ Icc (-r) r : Set (E × ℝ)) => c z) ∧
      IsOpen (c '' (K' ×ˢ Ioo (-r) r)) ∧
      c '' (K' ×ˢ ({0} : Set ℝ)) = F ∩ P ∧
      (∀ z ∈ K' ×ˢ Icc (-r) r, c z ∈ P ↔ 0 ≤ z.2) ∧
      (K'.Nonempty ↔ (F ∩ P).Nonempty) ∧
      (frontier P ⊆ F → c '' (K' ×ˢ ({0} : Set ℝ)) = frontier P) := by
  intro P K'
  let : LocallyPathConnectedSpace R := he.locallyPathConnectedSpace
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hPc : IsCompact P := Set.isCompact_connectedComponentIn_of_mem hR hx
  have hPo : IsOpen ((Subtype.val : R → X) ⁻¹' P) :=
    Set.isOpen_preimage_connectedComponentIn hx
  have hc : ContinuousOn c (K ×ˢ Icc (-r) r) :=
    continuousOn_iff_continuous_domRestrict.mpr hi.continuous
  have hbaseR (z : K) : c ((z : E), 0) ∈ R :=
    he.closed.frontier_subset (hF (hzero.subset ⟨(z, 0), ⟨z.2, rfl⟩, rfl⟩))
  have hc0 : Continuous (fun z : K => c ((z : E), 0)) :=
    hc.comp_continuous (continuous_subtype_val.prodMk continuous_const)
      (fun z => ⟨z.2, neg_nonpos.mpr hr.le, hr.le⟩)
  let base : C(K, R) := ⟨fun z => ⟨c ((z : E), 0), hbaseR z⟩, hc0.subtype_mk _⟩
  let J : Set K := base ⁻¹' ((Subtype.val : R → X) ⁻¹' P)
  have hJ : IsClopen J :=
    ⟨hPc.isClosed.preimage hc0, hPo.preimage base.continuous⟩
  have hJpre : J = (Subtype.val : K → E) ⁻¹' K' := by
    ext z
    exact ⟨fun h => ⟨z.2, h⟩, fun h => h.2⟩
  have hJim : (Subtype.val : K → E) '' J = K' := by
    ext z
    exact ⟨fun ⟨w, hw, hwz⟩ => hwz ▸ ⟨w.2, hw⟩,
      fun hz => ⟨⟨z, hz.1⟩, hz.2, rfl⟩⟩
  have hKc : IsCompact K' := hJim ▸ hJ.isClosed.isCompact.image continuous_subtype_val
  have hsub : K' ⊆ K := fun _ hz => hz.1
  have hprod : K' ×ˢ Icc (-r) r ⊆ K ×ˢ Icc (-r) r := prod_mono hsub subset_rfl
  have hzero' : c '' (K' ×ˢ ({0} : Set ℝ)) = F ∩ P := by
    ext y
    constructor
    · rintro ⟨⟨z, t⟩, ⟨hz, ht⟩, rfl⟩
      have ht0 : t = 0 := ht
      subst t
      exact ⟨hzero.subset ⟨(z, 0), ⟨hz.1, rfl⟩, rfl⟩, hz.2⟩
    · rintro ⟨hyF, hyP⟩
      obtain ⟨⟨z, t⟩, ⟨hz, ht⟩, hzy⟩ := hzero.symm.subset hyF
      have ht0 : t = 0 := ht
      subst t
      exact ⟨(z, 0), ⟨⟨hz, hzy ▸ hyP⟩, rfl⟩, hzy⟩
  refine ⟨hPc, he.connectedComponentIn hR hx, hKc, hJpre ▸ hJ,
    hi.comp (IsEmbedding.inclusion hprod), ?_, hzero', ?_, ?_, ?_⟩
  · let A : Set (E × ℝ) := K ×ˢ Icc (-r) r
    let first : C(A, K) := ⟨fun z => ⟨z.1.1, z.2.1⟩, by fun_prop⟩
    let time : C(A, ℝ) := ⟨fun z => z.1.2, by fun_prop⟩
    let V : Set A := first ⁻¹' J ∩ time ⁻¹' Ioo (-r) r
    have hV : IsOpen V := (hJ.isOpen.preimage first.continuous).inter
      (isOpen_Ioo.preimage time.continuous)
    let f : A → X := fun z => c z
    have hVW : f '' V ⊆ c '' (K ×ˢ Ioo (-r) r) := by
      rintro _ ⟨z, hz, rfl⟩
      exact ⟨z, ⟨z.2.1, hz.2⟩, rfl⟩
    have hWr : c '' (K ×ˢ Ioo (-r) r) ⊆ range f := by
      rintro _ ⟨z, hz, rfl⟩
      exact ⟨⟨z, hz.1, hz.2.1.le, hz.2.2.le⟩, rfl⟩
    have himage : f '' V = c '' (K' ×ˢ Ioo (-r) r) := by
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact ⟨z, ⟨⟨z.2.1, hz.1⟩, hz.2⟩, rfl⟩
      · rintro ⟨z, hz, rfl⟩
        exact ⟨⟨z, hz.1.1, hz.2.1.le, hz.2.2.le⟩, ⟨hz.1.2, hz.2⟩, rfl⟩
    rw [← himage]
    exact hi.isInducing.isOpen_image_of_subset_open hV hopen hVW hWr
  · exact signed_collar_side_on_connectedComponentIn c (hc.mono hprod)
      (fun z hz => hside z (hprod hz)) (fun z hz => hz.2)
  · constructor
    · rintro ⟨z, hz⟩
      exact ⟨c (z, 0), hzero'.subset ⟨(z, 0), ⟨hz, rfl⟩, rfl⟩⟩
    · rintro ⟨y, hy⟩
      obtain ⟨z, hz, _⟩ := hzero'.symm.subset hy
      exact ⟨z.1, hz.1⟩
  · intro hfront
    obtain ⟨U, hU, hPU⟩ := Set.exists_open_inter_of_relative_open
      (connectedComponentIn_subset R x) hPo
    have hPF : frontier P = P ∩ frontier R :=
      Set.frontier_eq_inter_of_eq_inter_open he.closed hPc.isClosed hU hPU
    rw [hzero']
    apply subset_antisymm
    · intro y hy
      rw [hPF]
      exact ⟨hy.2, hF hy.1⟩
    · intro y hy
      exact ⟨hfront hy, (hPF.subset hy).1⟩

end PoincareConjecture.M76
