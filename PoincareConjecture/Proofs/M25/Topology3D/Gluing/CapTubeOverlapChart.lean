import PoincareConjecture.Proofs.M25.AppA_21_Local.CapTubeEnds
import PoincareConjecture.Proofs.M25.Mathlib.CylinderTail
import Mathlib.Topology.OpenPartialHomeomorph.Constructions
import Mathlib.Geometry.Manifold.ContMDiff.Basic











set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M25.Topology3D




theorem capTubeAttachment_exists_cofinalOverlapChart
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
    [T3Space M] {g : RiemannianMetric 3 M}
    {X : Set M} {C : CapCertificate g}
    {T : EpsilonTubeCertificate g X} {side : Bool}
    (A : CapTubeAttachment C T side) :
    let U : TopologicalSpace.Opens M :=
      ⟨C.carrier, C.carrier_open⟩
    ∃ (omega : Bool) (e : OpenPartialHomeomorph RoundCylinderSpace U),
      e.source = univ ×ˢ Ioo (0 : ℝ) 1 ∧
      e.target = (Subtype.val : U → M) ⁻¹' T.carrier ∧
      (∀ z ∈ e.source,
        (e z).val = A.overlap_model.coordinate
          (z.1, if omega then z.2 else 1 - z.2)) ∧
      (∀ x ∈ e.target,
        e.symm x = ((A.overlap_model.inverse x.val).1,
          if omega then (A.overlap_model.inverse x.val).2
          else 1 - (A.overlap_model.inverse x.val).2)) ∧
      ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ e e.source ∧
      ContMDiffOn (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ e.symm e.target ∧
      (∀ d ∈ Ioo (0 : ℝ) 1,
        (Subtype.val : U → M) '' e.cylinderTail 1 d =
          A.overlap_model.tail omega (if omega then d else 1 - d)) ∧
      (∀ d ∈ Ioo (0 : ℝ) 1,
        IsCompact (e.cylinderTail 1 d)ᶜ) := by
  classical
  let U : TopologicalSpace.Opens M := ⟨C.carrier, C.carrier_open⟩
  change ∃ (omega : Bool) (e : OpenPartialHomeomorph RoundCylinderSpace U), _
  let B := A.overlap_model
  let Omega : Set RoundCylinderSpace := univ ×ˢ Ioo (0 : ℝ) 1
  let O := C.carrier ∩ T.carrier
  obtain ⟨_, omega, _, _, hcompact, _⟩ := A.exists_cofinal_overlap_end
  let J : RoundCylinderSpace → RoundCylinderSpace :=
    fun z => (z.1, if omega then z.2 else 1 - z.2)
  have hJ : ContMDiff ((𝓡 2).prod 𝓘(ℝ, ℝ))
      ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ J := by
    cases omega with
    | false => exact contMDiff_fst.prodMk (contMDiff_const.sub contMDiff_snd)
    | true => exact contMDiff_id
  have hJJ (z : RoundCylinderSpace) : J (J z) = z := by
    cases omega <;> simp [J]
  have hJmem : MapsTo J Omega Omega := by
    intro z hz
    refine ⟨mem_univ _, ?_⟩
    cases omega with
    | false =>
      change 0 < 1 - z.2 ∧ 1 - z.2 < 1
      constructor <;> linarith [hz.2.1, hz.2.2]
    | true => exact hz.2
  have hB : MapsTo B.coordinate Omega O := by
    intro z hz
    rw [← B.coordinate_eq (z.1, ⟨z.2, hz.2⟩)]
    exact (B.homeomorph (z.1, ⟨z.2, hz.2⟩)).property
  have hmap : ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞
      (fun z => B.coordinate (J z)) Omega :=
    B.coordinate_smooth.comp hJ.contMDiffOn hJmem
  have hback : ContMDiffOn (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞
      (fun x => J (B.inverse x)) O :=
    hJ.comp_contMDiffOn B.inverse_smooth
  let e0 : OpenPartialHomeomorph RoundCylinderSpace M :=
    { toFun := fun z => B.coordinate (J z)
      invFun := fun x => J (B.inverse x)
      source := Omega
      target := O
      map_source' := fun _ hz => hB (hJmem hz)
      map_target' := fun _ hx => hJmem (B.inverse_mem _ hx)
      left_inv' := by
        intro z hz
        rw [B.left_inverse (hJmem hz), hJJ]
      right_inv' := by
        intro x hx
        rw [hJJ]
        exact B.right_inverse hx
      open_source := isOpen_univ.prod isOpen_Ioo
      open_target := C.carrier_open.inter T.carrier_open
      continuousOn_toFun := hmap.continuousOn
      continuousOn_invFun := hback.continuousOn }
  have hU : Nonempty U := ⟨⟨C.end_neck.center,
    C.end_neck_subset
      (C.end_neck.central_sphere_subset C.end_neck.center_on_central_sphere)⟩⟩
  let f := e0.symm
  let e : OpenPartialHomeomorph RoundCylinderSpace U := (f.subtypeRestr hU).symm
  have hsource : e.source = univ ×ˢ Ioo (0 : ℝ) 1 := by
    change (f.subtypeRestr hU).target = _
    rw [OpenPartialHomeomorph.subtypeRestr_def, OpenPartialHomeomorph.trans_target,
      U.openPartialHomeomorphSubtypeCoe_target]
    ext z
    change (z ∈ Omega ∧ B.coordinate (J z) ∈ C.carrier) ↔ z ∈ Omega
    exact ⟨fun hz => hz.1, fun hz => ⟨hz, (hB (hJmem hz)).1⟩⟩
  have htarget : e.target = (Subtype.val : U → M) ⁻¹' T.carrier := by
    change (f.subtypeRestr hU).source = _
    rw [f.subtypeRestr_source]
    ext x
    change (x.val ∈ C.carrier ∧ x.val ∈ T.carrier) ↔ x.val ∈ T.carrier
    exact ⟨fun hx => hx.2, fun hx => ⟨x.property, hx⟩⟩
  have hforward : ∀ z ∈ e.source, (e z).val = B.coordinate (J z) := by
    intro z hz
    exact f.subtypeRestr_symm_apply hU hz
  have hinverse : ∀ x : U, e.symm x = J (B.inverse x.val) := fun _ => rfl
  have he : ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ e e.source := by
    have hmap' : ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞
        (fun z => B.coordinate (J z)) e.source := by
      simpa only [hsource] using hmap
    have hcomp : ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞
        (Subtype.val ∘ e) e.source := hmap'.congr hforward
    intro z hz
    exact (ContMDiffWithinAt.subtypeVal_comp_iff U e e.source z).mp (hcomp z hz)
  have hei : ContMDiffOn (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ e.symm e.target := by
    change ContMDiffOn (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞
      (fun x : U => J (B.inverse x.val)) e.target
    apply hback.comp contMDiff_subtype_val.contMDiffOn
    intro x hx
    exact ⟨x.property, by simpa only [htarget, mem_preimage] using hx⟩
  have htail : ∀ d ∈ Ioo (0 : ℝ) 1,
      (Subtype.val : U → M) '' e.cylinderTail 1 d =
        B.tail omega (if omega then d else 1 - d) := by
    intro d hd
    have hdom : univ ×ˢ Ioo d 1 ⊆ e.source :=
      e.cylinderTail_domain_subset hsource hd.1
    have hJtail : J '' (univ ×ˢ Ioo d 1) =
        univ ×ˢ (if omega then Ioo d 1 else Ioo 0 (1 - d)) := by
      cases omega with
      | true => simp [J]
      | false =>
        ext z
        constructor
        · rintro ⟨w, hw, rfl⟩
          change J w ∈ univ ×ˢ Ioo 0 (1 - d)
          refine ⟨mem_univ _, ?_, ?_⟩
          · change 0 < 1 - w.2
            linarith [hw.2.2]
          · change 1 - w.2 < 1 - d
            linarith [hw.2.1]
        · intro hz
          change z ∈ univ ×ˢ Ioo 0 (1 - d) at hz
          refine ⟨J z, ⟨mem_univ _, ?_, ?_⟩, hJJ z⟩
          · change d < 1 - z.2
            linarith [hz.2.2]
          · change 1 - z.2 < 1
            linarith [hz.2.1]
    calc
      (Subtype.val : U → M) '' e.cylinderTail 1 d =
          (Subtype.val ∘ e) '' (univ ×ˢ Ioo d 1) := image_image _ _ _
      _ = (B.coordinate ∘ J) '' (univ ×ˢ Ioo d 1) :=
        image_congr (fun z hz => hforward z (hdom hz))
      _ = B.coordinate '' (J '' (univ ×ˢ Ioo d 1)) :=
        (image_image B.coordinate J (univ ×ˢ Ioo d 1)).symm
      _ = B.tail omega (if omega then d else 1 - d) := by
        rw [hJtail]
        cases omega <;> rfl
  refine ⟨omega, e, hsource, htarget, hforward, fun x _ => hinverse x,
    he, hei, htail, ?_⟩
  intro d hd
  have hd' : (if omega then d else 1 - d) ∈ Ioo (0 : ℝ) 1 := by
    cases omega with
    | false =>
      change 0 < 1 - d ∧ 1 - d < 1
      constructor <;> linarith [hd.1, hd.2]
    | true => exact hd
  have himage : (Subtype.val : U → M) '' (e.cylinderTail 1 d)ᶜ =
      C.carrier \ B.tail omega (if omega then d else 1 - d) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨y.property, ?_⟩
      intro hm
      rw [← htail d hd] at hm
      obtain ⟨z, hz, hzy⟩ := hm
      have hzy' : z = y := Subtype.ext hzy
      exact hy (hzy' ▸ hz)
    · intro hx
      refine ⟨⟨x, hx.1⟩, ?_, rfl⟩
      intro hm
      apply hx.2
      rw [← htail d hd]
      exact ⟨⟨x, hx.1⟩, hm, rfl⟩
  apply Subtype.isCompact_iff.mpr
  rw [himage]
  exact hcompact _ hd'

end PoincareConjecture.M25.Topology3D
