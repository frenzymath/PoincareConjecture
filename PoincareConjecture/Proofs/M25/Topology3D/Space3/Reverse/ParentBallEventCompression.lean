import PoincareConjecture.Proofs.M25.Topology3D.Space3.Reverse.ParentBallEventSupport
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Reverse.ParentBallEventCapGerm
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Reverse.ParentBallCommonCap











set_option autoImplicit false

open Set Metric Filter
open scoped ContDiff Manifold Topology InnerProductSpace

namespace PoincareConjecture.M25.Topology3D


theorem RegularSurgeryEvent.exists_supported_child_compression
    {parent : UnitTwoSphere × ℝ → E3} {u : UnitTwoSphere}
    (E : RegularSurgeryEvent parent u)
    (A : Fin 2 → BallNeighborhoodChart E3 E3)
    (hboundary : ∀ k : Fin 2,
      (A k).boundary = E.child k '' (univ ×ˢ ({0} : Set ℝ))) :
    let a := E.data.width / 2 * (1 - E.radius)
    let core : Fin 2 → Set E3 := fun k =>
      (fun q : UnitTwoSphere => parent (q, 0)) ''
        ((![E.data.sourceDiscs.positive, E.data.sourceDiscs.negative] k) ''
          closedBall (0 : E2) E.radius)
    let annulus := E.data.tube ''
      (sphere (0 : E2) 1 ×ˢ Ioo (E.cutHeight - a) (E.cutHeight + a))
    let annulusClosed := E.data.tube ''
      (sphere (0 : E2) 1 ×ˢ Icc (E.cutHeight - a) (E.cutHeight + a))
    ∃ i : Fin 2,
      let j : Fin 2 := ![1, 0] i
      let M := E.canonicalCapBall j
      let north := E.profile.capMap E.data.tube E.cutHeight
        (![1, -1] j) a E.scale ''
          {q : UnitTwoSphere | 0 ≤ (heightCoordinates (q : E3)).2}
      (Disjoint (A i).closedRegion (A j).closedRegion ∨
        (A j).closedRegion ⊆ (A i).inside) ∧
      ∃ Ω : Set E3, IsOpen Ω ∧
        (Disjoint (A i).closedRegion (A j).closedRegion →
          Ω = ((A i).closedRegion ∪ annulusClosed)ᶜ) ∧
        (¬Disjoint (A i).closedRegion (A j).closedRegion →
          Ω = (A i).inside \ annulusClosed) ∧
        ∃ H : Diffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 E3 ∞,
          ∃ S : Set E3, IsCompact S ∧ S ⊆ Ω \ (E.newCap j).cap ∧
            tsupport (fun y => H y - y) ⊆ S ∧
            tsupport (fun y => H.symm y - y) ⊆ S ∧
            H '' (A j).inside = M.inside ∧
            H '' (A j).closedRegion = M.closedRegion ∧
            H '' (A j).boundary = M.boundary ∧
            (∀ y ∈ (A i).boundary ∪ annulusClosed ∪ (E.newCap j).cap,
              H y = y ∧ H.symm y = y) ∧
            H '' (A i).inside = (A i).inside ∧
            H '' (A i).closedRegion = (A i).closedRegion ∧
            H '' (A i).boundary = (A i).boundary ∧
            (Disjoint (A i).closedRegion (A j).closedRegion →
              ∀ y ∈ (A i).closedRegion, H y = y ∧ H.symm y = y) ∧
            (¬Disjoint (A i).closedRegion (A j).closedRegion → S ⊆ (A i).inside) ∧
            H '' core j = north ∧
            H '' (parent '' (univ ×ˢ ({0} : Set ℝ))) = core i ∪ annulus ∪ north ∧
            ∃ A' : BallNeighborhoodChart E3 E3,
              A'.inside = (A j).inside ∧ A'.closedRegion = (A j).closedRegion ∧
              A'.boundary = (A j).boundary ∧
              ∃ g : Diffeomorph (𝓡 2) (𝓡 2) UnitTwoSphere UnitTwoSphere ∞,
                (∀ q : UnitTwoSphere, A'.chart (g q : E3) = E.child j (q, 0)) ∧
                ∃ G : Diffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 E3 ∞,
                  (∀ y : E3, ‖G y‖ = ‖y‖) ∧
                  (∀ x ∈ closedBall (0 : E3) 1,
                    H (A'.chart x) = M.chart (G x)) ∧
                  ∀ q : UnitTwoSphere,
                    H (E.child j (q, 0)) = M.chart (G (g q : E3)) := by
  classical
  let a := E.data.width / 2 * (1 - E.radius)
  let core : Fin 2 → Set E3 := fun k =>
    (fun q : UnitTwoSphere => parent (q, 0)) ''
      ((![E.data.sourceDiscs.positive, E.data.sourceDiscs.negative] k) ''
        closedBall (0 : E2) E.radius)
  let annulus := E.data.tube ''
    (sphere (0 : E2) 1 ×ˢ Ioo (E.cutHeight - a) (E.cutHeight + a))
  let annulusClosed := E.data.tube ''
    (sphere (0 : E2) 1 ×ˢ Icc (E.cutHeight - a) (E.cutHeight + a))
  obtain ⟨i, hregions, b, hb, N, hN, _hAcap, g, _hg, R, _hR, _hRsource, _hRheight,
      G, hG, _hGpoint, _hGimage, B, hBc, hBi, hBcl, hBb, _hBcap,
      F, _hFfix, _hFball, _hFclosed, A', _hA'c, hA'i, hA'cl, hA'b, _hA'point,
      hg, hA'cap, hBA, hgerm⟩ := E.exists_common_cap_ball_charts A hboundary
  let j : Fin 2 := ![1, 0] i
  let M := E.canonicalCapBall j
  let north := E.profile.capMap E.data.tube E.cutHeight (![1, -1] j) a E.scale ''
    {q : UnitTwoSphere | 0 ≤ (heightCoordinates (q : E3)).2}
  let Db := {y : E3 | ‖y‖ = 1 ∧ b ≤ (heightCoordinates y).2}
  let v : E3 := EuclideanSpace.single (2 : Fin 3) 1
  have hv : ‖v‖ = 1 := by simp [v]
  have hDb : {x : E3 | ‖x‖ = 1 ∧ b ≤ ⟪v, x⟫_ℝ} = Db := by
    ext x
    simp only [v, Db, EuclideanSpace.inner_single_left, map_one, one_mul,
      heightCoordinates_snd_apply]
  obtain ⟨_hcompact, _hcapAnn, Ω, hΩ, hΩdis, hΩnest, hAΩ, hΩavoid⟩ :=
    E.exists_compression_support_domain A hboundary i hregions
  have hcommon : ∀ᶠ x in 𝓝ˢ {x : E3 | ‖x‖ = 1 ∧ b ≤ ⟪v, x⟫_ℝ},
      A'.chart x = B.chart x := by
    rw [hDb]
    exact hgerm.mono (fun _ h => h.2.2)
  have hA'Ω : A'.closedRegion \ (A'.chart ''
      {x : E3 | ‖x‖ = 1 ∧ b ≤ ⟪v, x⟫_ℝ}) ⊆ Ω := by
    rw [hDb, hA'cap, hA'cl]
    exact hAΩ
  have hBΩ : B.closedRegion \ (A'.chart ''
      {x : E3 | ‖x‖ = 1 ∧ b ≤ ⟪v, x⟫_ℝ}) ⊆ Ω :=
    (sdiff_subset_sdiff_left hBA).trans hA'Ω
  obtain ⟨H, hpoint, hHi, hHcl, hHb, _hcapFix, S, hS, hSΩ, hfix⟩ :=
    exists_ball_transport_of_common_cap_germ A' B v hv b hb hcommon hΩ hA'Ω hBΩ
  rw [hDb, hA'cap] at hSΩ
  rw [hA'i, hBi] at hHi
  rw [hA'cl, hBcl] at hHcl
  rw [hA'b, hBb] at hHb
  have hout (y : E3) (hy : y ∉ S) : H y = y ∧ H.symm y = y :=
    ⟨hfix y hy, equiv_symm_fixed_of_fixed H.toEquiv (hfix y hy)⟩
  have hs : tsupport (fun y => H y - y) ⊆ S := by
    apply closure_minimal _ hS.isClosed
    intro y hy
    by_contra hn
    exact hy (sub_eq_zero.mpr (hout y hn).1)
  have his : tsupport (fun y => H.symm y - y) ⊆ S := by
    apply closure_minimal _ hS.isClosed
    intro y hy
    by_contra hn
    exact hy (sub_eq_zero.mpr (hout y hn).2)
  have hprotected (y : E3)
      (hy : y ∈ (A i).boundary ∪ annulusClosed ∪ (E.newCap j).cap) :
      H y = y ∧ H.symm y = y := by
    apply hout
    intro hyS
    exact hy.elim
      (fun h => disjoint_left.mp hΩavoid (hSΩ hyS).1 h)
      (fun h => (hSΩ hyS).2 h)
  have hstationaryPoint (hd : Disjoint (A i).closedRegion (A j).closedRegion)
      (y : E3) (hy : y ∈ (A i).closedRegion) : H y = y ∧ H.symm y = y := by
    apply hout
    intro hyS
    have hyΩ := (hSΩ hyS).1
    rw [hΩdis hd] at hyΩ
    exact hyΩ (Or.inl hy)
  have hSnest (hd : ¬Disjoint (A i).closedRegion (A j).closedRegion) :
      S ⊆ (A i).inside := by
    intro y hy
    have hyΩ := (hSΩ hy).1
    rw [hΩnest hd] at hyΩ
    exact hyΩ.1
  have himageFixed (D : Set E3) (hD : ∀ y ∈ D, H y = y) : H '' D = D := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [hD x hx]
      exact hx
    · intro hy
      exact ⟨y, hy, hD y hy⟩
  have hstationaryInside : H '' (A i).inside = (A i).inside := by
    by_cases hd : Disjoint (A i).closedRegion (A j).closedRegion
    · exact himageFixed _ (fun y hy =>
        (hstationaryPoint hd y (image_mono ball_subset_closedBall hy)).1)
    · have hmap : MapsTo H (A i).inside (A i).inside :=
        equiv_mapsTo_of_fixed_compl H.toEquiv
          (fun y hy => (hout y (fun h => hy (hSnest hd h))).1)
      have himap : MapsTo H.symm (A i).inside (A i).inside :=
        equiv_mapsTo_of_fixed_compl H.toEquiv.symm
          (fun y hy => (hout y (fun h => hy (hSnest hd h))).2)
      apply Subset.antisymm
      · rintro y ⟨x, hx, rfl⟩
        exact hmap hx
      · intro y hy
        exact ⟨H.symm y, himap hy, H.apply_symm_apply y⟩
  have hstationaryClosed : H '' (A i).closedRegion = (A i).closedRegion := by
    rw [← (A i).closure_inside]
    change H.toHomeomorph '' closure (A i).inside = closure (A i).inside
    rw [H.toHomeomorph.image_closure]
    change closure (H '' (A i).inside) = closure (A i).inside
    rw [hstationaryInside]
  have hstationaryBoundary : H '' (A i).boundary = (A i).boundary :=
    himageFixed _ (fun y hy => (hprotected y (Or.inl (Or.inl hy))).1)
  obtain ⟨hparent, _hcoreAnnulus, _hcores, hcover, hinter, _hchildren⟩ := E.region_identities
  obtain ⟨_hMc, _hMs, _hMt, _hMf, _hMi, _hMq, _hMsouth, _hMnorth,
      hMboundary, hMinter, _hMrest⟩ := E.canonicalCapBall_spec j
  have hseamNorth : (E.newCap j).seam ⊆ north := by
    intro y hy
    rw [← hMinter] at hy
    exact hy.2
  have hcoreImage : H '' core j = north := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hxB : x ∈ (A j).boundary := by
        rw [hboundary j, hcover j]
        exact Or.inl hx
      have hyB : H x ∈ M.boundary := by
        rw [← hHb]
        exact ⟨x, hxB, rfl⟩
      rw [hMboundary] at hyB
      rcases hyB with hyCap | hyNorth
      · have hxy : x = H x :=
          H.injective (hprotected (H x) (Or.inr hyCap)).1.symm
        rw [← hxy] at hyCap ⊢
        apply hseamNorth
        rw [← hinter j]
        exact ⟨hx, hyCap⟩
      · exact hyNorth
    · intro hy
      have hyB : y ∈ M.boundary := by rw [hMboundary]; exact Or.inr hy
      rw [← hHb] at hyB
      obtain ⟨x, hxB, hxy⟩ := hyB
      rw [hboundary j, hcover j] at hxB
      rcases hxB with hxCore | hxCap
      · exact ⟨x, hxCore, hxy⟩
      · have hxy' : x = y := (hprotected x (Or.inr hxCap)).1.symm.trans hxy
        have hxNorth : x ∈ north := hxy'.symm ▸ hy
        refine ⟨x, ?_, hxy⟩
        have hxSeam : x ∈ (E.newCap j).seam := by
          rw [← hMinter]
          exact ⟨hxCap, hxNorth⟩
        rw [← hinter j] at hxSeam
        exact hxSeam.1
  have hstationaryCore : H '' core i = core i := by
    apply himageFixed
    intro y hy
    apply (hprotected y ?_).1
    left
    left
    rw [hboundary i, hcover i]
    exact Or.inl hy
  have hAnn : H '' annulus = annulus := by
    apply himageFixed
    intro y hy
    apply (hprotected y ?_).1
    exact Or.inl (Or.inr (image_mono (prod_mono_right Ioo_subset_Icc_self) hy))
  have hcoreOrder : core 0 ∪ core 1 = core i ∪ core j := by
    fin_cases i
    · rfl
    · exact union_comm _ _
  have hparentImage : H '' (parent '' (univ ×ˢ ({0} : Set ℝ))) =
      core i ∪ annulus ∪ north := by
    change parent '' (univ ×ˢ ({0} : Set ℝ)) = core 0 ∪ core 1 ∪ annulus at hparent
    rw [hparent, hcoreOrder, image_union, image_union, hstationaryCore, hcoreImage, hAnn]
    ac_rfl
  have hcomparison (x : E3) (hx : x ∈ closedBall (0 : E3) 1) :
      H (A'.chart x) = M.chart (G x) := by
    rw [hpoint x hx, hBc]
    rfl
  refine ⟨i, hregions, Ω, hΩ, hΩdis, hΩnest, H, S, hS, hSΩ, hs, his,
    hHi, hHcl, hHb, hprotected, hstationaryInside, hstationaryClosed,
    hstationaryBoundary, hstationaryPoint, hSnest, hcoreImage, hparentImage,
    A', hA'i, hA'cl, hA'b, g, hg, G, hG, hcomparison, ?_⟩
  intro q
  rw [← hg q]
  exact hcomparison (g q : E3) (sphere_subset_closedBall (g q).property)

end PoincareConjecture.M25.Topology3D
