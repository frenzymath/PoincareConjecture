import PoincareConjecture.Proofs.M25.Topology3D.Gluing.ProjectiveDoubleClosedModel.NegativeMatching
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.OpenEmbedding
import PoincareConjecture.Proofs.M07.Geometry.Manifold.LocalDiffeomorph










set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M25.Topology3D

variable {M : Type u} [TopologicalSpace M] [ChartedSpace E3 M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T3Space M] {g : RiemannianMetric 3 M} {C1 C2 : ClosedModelCapData g}
  {P2 : PoincareConjecture.StandardPuncturedProjectiveCover M C2.puncture C2.carrier}




theorem NegativeProjectiveSideData.nonempty_smooth_cover
    (hS : SchoenfliesService) (hD : DiffSphereIsotopyService)
    (P1 : PoincareConjecture.StandardPuncturedProjectiveCover M C1.puncture C1.carrier)
    (d : NegativeProjectiveSideData C1 C2 P2) :
    let U : TopologicalSpace.Opens M :=
      ⟨C1.carrier ∪ C2.carrier, C1.carrier_open.union C2.carrier_open⟩
    Nonempty (PoincareConjecture.StandardProjectiveSmoothCover U) := by
  classical
  let P := P1
  obtain ⟨F, G, hG, hGi, hcover, hinter, hmatch, hpre,
    hUopen, hUneg, hdis, hwhole, hUinter⟩ :=
    NegativeProjectiveSideData.exists_matched_ball hS hD P1 d
  let ell := C1.epsilon⁻¹
  let c := (d.v + ell) / 2
  let h := (ell - d.v) / 4
  let a := c - h * (3 / 4)
  let b := c - h * (1 / 2)
  let V : Set M := interior (C1.carrier \ C1.region b ell)
  let L : Set UnitThreeSphere := F '' (univ ×ˢ Ioo a b)
  let U0 : Set UnitThreeSphere := projectiveCoverDomain C1.puncture ∩ P.cover ⁻¹' V
  let B : Set UnitThreeSphere := G.source
  let U : TopologicalSpace.Opens M :=
    ⟨C1.carrier ∪ C2.carrier, C1.carrier_open.union C2.carrier_open⟩
  change Nonempty (PoincareConjecture.StandardProjectiveSmoothCover U)
  change V ∪ G.target = C1.carrier ∪ C2.carrier at hcover
  change V ∩ G.target = C1.region a b at hinter
  change EqOn G P.cover L at hmatch
  change B ∩ G ⁻¹' C1.region a b = L at hpre
  change IsOpen U0 at hUopen
  change ∀ x : UnitThreeSphere, -x ∈ U0 ↔ x ∈ U0 at hUneg
  change Disjoint B ((fun x : UnitThreeSphere => -x) '' B) at hdis
  change U0 ∪ B ∪ (fun x : UnitThreeSphere => -x) '' B = univ at hwhole
  change U0 ∩ B = L at hUinter
  have hnotboth (x : UnitThreeSphere) (hx : x ∈ B) : -x ∉ B := by
    intro hnx
    exact disjoint_left.mp hdis hx ⟨-x, hnx, neg_neg x⟩
  have hdomains (x : UnitThreeSphere) : x ∈ U0 ∨ x ∈ B ∨ -x ∈ B := by
    have hx : x ∈ U0 ∪ B ∪ (fun y : UnitThreeSphere => -y) '' B :=
      hwhole.symm ▸ mem_univ x
    rcases hx with (hx | hx) | ⟨y, hy, rfl⟩
    · exact Or.inl hx
    · exact Or.inr (Or.inl hx)
    · exact Or.inr (Or.inr (by simpa only [neg_neg] using hy))
  let H : UnitThreeSphere → M := fun x =>
    if x ∈ B then G x else if -x ∈ B then G (-x) else P.cover x
  have hHB (x : UnitThreeSphere) (hx : x ∈ B) : H x = G x := by
    simp only [H, if_pos hx]
  have hHN (x : UnitThreeSphere) (hx : -x ∈ B) : H x = G (-x) := by
    have hxnot : x ∉ B := fun hxb => hnotboth x hxb hx
    simp only [H, if_neg hxnot, if_pos hx]
  have hHU (x : UnitThreeSphere) (hx : x ∈ U0) : H x = P.cover x := by
    by_cases hxb : x ∈ B
    · exact (hHB x hxb).trans (hmatch (hUinter ▸ ⟨hx, hxb⟩))
    by_cases hxnb : -x ∈ B
    · exact (hHN x hxnb).trans ((hmatch (hUinter ▸ ⟨(hUneg x).mpr hx, hxnb⟩)).trans
        (StandardPuncturedProjectiveCover.cover_neg P hx.1))
    · simp only [H, if_neg hxb, if_neg hxnb]
  have hHneg (x : UnitThreeSphere) : H (-x) = H x := by
    by_cases hx : x ∈ B
    · have hn : H (-x) = G x := by
        simpa only [neg_neg] using hHN (-x) (by simpa only [neg_neg] using hx)
      exact hn.trans (hHB x hx).symm
    by_cases hnx : -x ∈ B
    · exact (hHB (-x) hnx).trans (hHN x hnx).symm
    have hxU : x ∈ U0 := (hdomains x).resolve_right (fun h => h.elim hx hnx)
    exact (hHU (-x) ((hUneg x).mpr hxU)).trans
      ((StandardPuncturedProjectiveCover.cover_neg P hxU.1).trans (hHU x hxU).symm)
  have hVcap : V ⊆ C1.carrier := fun _ hx => (interior_subset hx).1
  have hHmem (x : UnitThreeSphere) : H x ∈ (U : Set M) := by
    rcases hdomains x with hx | hx | hx
    · rw [hHU x hx]
      exact Or.inl (hVcap hx.2)
    · rw [hHB x hx]
      change G x ∈ C1.carrier ∪ C2.carrier
      rw [← hcover]
      exact Or.inr (G.map_source hx)
    · rw [hHN x hx]
      change G (-x) ∈ C1.carrier ∪ C2.carrier
      rw [← hcover]
      exact Or.inr (G.map_source hx)
  let Hc : UnitThreeSphere → U := fun x => ⟨H x, hHmem x⟩
  let dG : PartialDiffeomorph (𝓡 3) (𝓡 3) UnitThreeSphere M ∞ :=
    { toPartialEquiv := G.toPartialEquiv
      open_source := G.open_source
      open_target := G.open_target
      contMDiffOn_toFun := hG
      contMDiffOn_invFun := hGi }
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 4)) = 3 + 1) := ⟨by simp⟩
  let dn : Diffeomorph (𝓡 3) (𝓡 3) UnitThreeSphere UnitThreeSphere ∞ :=
    { toEquiv :=
        { toFun := fun x => -x
          invFun := fun x => -x
          left_inv := neg_neg
          right_inv := neg_neg }
      contMDiff_toFun := contMDiff_neg_sphere
      contMDiff_invFun := contMDiff_neg_sphere }
  have hNopen : IsOpen {x : UnitThreeSphere | -x ∈ B} :=
    G.open_source.preimage dn.continuous
  have hHloc : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ H := by
    intro x
    rcases hdomains x with hx | hx | hx
    · exact (P.local_diffeomorph ⟨x, hx.1⟩).congr_of_eventuallyEq
        (Filter.eventuallyEq_of_mem (hUopen.mem_nhds hx) (fun y hy => hHU y hy))
    · have hg : IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ G x :=
        ⟨dG, hx, fun _ _ => rfl⟩
      exact hg.congr_of_eventuallyEq
        (Filter.eventuallyEq_of_mem (G.open_source.mem_nhds hx) (fun y hy => hHB y hy))
    · have hg : IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ G (-x) :=
        ⟨dG, hx, fun _ _ => rfl⟩
      have hc := (dn.isLocalDiffeomorph x).comp (𝓡 3) M hg
      exact hc.congr_of_eventuallyEq
        (Filter.eventuallyEq_of_mem (hNopen.mem_nhds hx) (fun y hy => hHN y hy))
  have hHcloc : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ Hc := by
    intro x
    have hi := Poincare.isLocalDiffeomorph_opensSubtypeVal (𝓡 3) U (Hc x)
    have hc := (hHloc x).comp (𝓡 3) U hi.localInverse_isLocalDiffeomorphAt
    apply hc.congr_of_eventuallyEq
    have hev : ∀ᶠ y in 𝓝 x, H y ∈ hi.localInverse.source :=
      hHloc.contMDiff.continuous.continuousAt
        (hi.localInverse_open_source.mem_nhds hi.localInverse_mem_source)
    filter_upwards [hev] with y hy
    apply Subtype.ext
    exact (hi.localInverse_right_inv hy).symm
  have hsurj : Function.Surjective Hc := by
    intro y
    have hy : y.val ∈ V ∪ G.target := hcover.symm ▸ y.property
    rcases hy with hy | hy
    · obtain ⟨x, hx, hxy⟩ := P.image_eq.symm ▸ hVcap hy
      have hxU : x ∈ U0 := ⟨hx, by change P.cover x ∈ V; rw [hxy]; exact hy⟩
      exact ⟨x, Subtype.ext ((hHU x hxU).trans hxy)⟩
    · exact ⟨G.symm y.val,
        Subtype.ext ((hHB _ (G.map_target hy)).trans (G.right_inv hy))⟩
  have hcross (x y : UnitThreeSphere) (hx : x ∈ U0) (hy : y ∈ B)
      (hxy : H x = H y) : x = y ∨ x = -y := by
    have heq : P.cover x = G y := (hHU x hx).symm.trans (hxy.trans (hHB y hy))
    have hyr : G y ∈ C1.region a b :=
      hinter ▸ ⟨heq ▸ hx.2, G.map_source hy⟩
    have hyL : y ∈ L := hpre ▸ ⟨hy, hyr⟩
    have hyU : y ∈ U0 := (hUinter.symm ▸ hyL).1
    apply (P.fibers x y hx.1 hyU.1).mp
    exact (hHU x hx).symm.trans (hxy.trans (hHU y hyU))
  have hsmall (x y : UnitThreeSphere) (hx : x ∈ U0 ∨ x ∈ B)
      (hy : y ∈ U0 ∨ y ∈ B) (hxy : H x = H y) : x = y ∨ x = -y := by
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · exact (P.fibers x y hx.1 hy.1).mp
        ((hHU x hx).symm.trans (hxy.trans (hHU y hy)))
    · exact hcross x y hx hy hxy
    · rcases hcross y x hy hx hxy.symm with heq | heq
      · exact Or.inl heq.symm
      · exact Or.inr (by simpa only [neg_neg] using
          (congrArg (fun z : UnitThreeSphere => -z) heq).symm)
    · exact Or.inl (G.injOn hx hy ((hHB x hx).symm.trans (hxy.trans (hHB y hy))))
  have hrep (x : UnitThreeSphere) :
      ∃ x' : UnitThreeSphere, (x' ∈ U0 ∨ x' ∈ B) ∧
        (x' = x ∨ x' = -x) ∧ H x' = H x := by
    rcases hdomains x with hx | hx | hx
    · exact ⟨x, Or.inl hx, Or.inl rfl, rfl⟩
    · exact ⟨x, Or.inr hx, Or.inl rfl, rfl⟩
    · exact ⟨-x, Or.inr hx, Or.inr rfl, hHneg x⟩
  have hfibers (x y : UnitThreeSphere) : H x = H y ↔ x = y ∨ x = -y := by
    constructor
    · intro hxy
      obtain ⟨x', hx', hsx, hHx⟩ := hrep x
      obtain ⟨y', hy', hsy, hHy⟩ := hrep y
      have hs := hsmall x' y' hx' hy' (hHx.trans (hxy.trans hHy.symm))
      rcases hsx with rfl | rfl <;> rcases hsy with rfl | rfl <;>
        rcases hs with heq | heq
      all_goals first
        | exact Or.inl heq
        | exact Or.inr heq
        | exact Or.inl (by simpa only [neg_neg] using heq)
        | exact Or.inr (by simpa only [neg_neg] using heq)
        | exact Or.inl (by simpa only [neg_neg] using
            (congrArg (fun z : UnitThreeSphere => -z) heq))
        | exact Or.inr (by simpa only [neg_neg] using
            (congrArg (fun z : UnitThreeSphere => -z) heq))
    · rintro (rfl | rfl)
      · rfl
      · exact hHneg y
  refine ⟨{ cover := Hc, surjective := hsurj, fibers := ?_, local_diffeomorph := hHcloc }⟩
  intro x y
  constructor
  · intro hxy
    exact (hfibers x y).mp (congrArg Subtype.val hxy)
  · intro hxy
    exact Subtype.ext ((hfibers x y).mpr hxy)

end PoincareConjecture.M25.Topology3D
