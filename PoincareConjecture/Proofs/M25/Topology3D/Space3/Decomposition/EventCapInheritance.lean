import PoincareConjecture.Proofs.M25.Topology3D.Space3.SurgeryEventRegions
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Decomposition.RetainedCapPlacement











set_option autoImplicit false

open Set Metric
open scoped ContDiff Manifold InnerProductSpace

namespace PoincareConjecture.M25.Topology3D.RegularSurgeryEvent


theorem exists_inherited_cap
    {parent : UnitTwoSphere × ℝ → E3} {u : UnitTwoSphere}
    (E : RegularSurgeryEvent parent u) (C : SurgeryCapTag parent u)
    (havoid : ∀ y ∈ C.cap,
      E.data.width ≤ |⟪(u : E3), y⟫_ℝ - E.cutHeight|) :
    ∃ i : Fin 2, ∃ C' : SurgeryCapTag (E.child i) u,
      C.sourceCap ⊆
        (![E.data.sourceDiscs.positive, E.data.sourceDiscs.negative] i) ''
          closedBall (0 : E2) E.radius ∧
      (∀ j : Fin 2, C.sourceCap ⊆
        (![E.data.sourceDiscs.positive, E.data.sourceDiscs.negative] j) ''
          closedBall (0 : E2) E.radius → j = i) ∧
      C'.profile = C.profile ∧ C'.tube = C.tube ∧
      C'.cutHeight = C.cutHeight ∧ C'.removal = C.removal ∧
      C'.scale = C.scale ∧ C'.sign = C.sign ∧
      C'.sourceChart = C.sourceChart.trans (E.retainedChart i).symm ∧
      C'.flatChart = C.flatChart.trans (E.retainedChart i).symm ∧
      C'.beta = C.beta * E.retainedTime i ∧
      C'.overlapWidth ≤ C.overlapWidth ∧
      C'.collarWidth = min 1 (C.collarWidth / (|E.retainedTime i| + 1)) ∧
      C'.cap = C.cap ∧ C'.seam = C.seam := by
  classical
  obtain ⟨i, hplace, hunique⟩ := C.exists_unique_retained_disc_of_height_avoidance
    E.cutHeight E.data E.radius_mem.1 E.radius_mem.2 E.radius_near E.radial havoid
  obtain ⟨hgamma, _hgammaSmall, _hsource, _htarget, _hmap, _hinverse,
    _hnorth, hcore, he, hei, heq⟩ := E.retained_spec i
  have hcap : C.sourceCap ⊆ (E.retainedChart i).target := hplace.trans hcore
  let C' : SurgeryCapTag (E.child i) u :=
    C.pullback (E.retainedChart i) he hei (E.retainedTime i) hgamma hcap heq
  refine ⟨i, C', hplace, hunique, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, ?_, rfl, ?_, ?_⟩
  · exact (Classical.choose_spec (C.exists_source_band_mem
      (E.retainedChart i).target (E.retainedChart i).open_target hcap)).2.1
  · exact C.pullback_cap (E.retainedChart i) he hei (E.retainedTime i) hgamma hcap heq
  · exact C.pullback_seam (E.retainedChart i) he hei (E.retainedTime i) hgamma hcap heq


theorem inherited_cap_disjoint_new
    {parent : UnitTwoSphere × ℝ → E3} {u : UnitTwoSphere}
    (E : RegularSurgeryEvent parent u) (C : SurgeryCapTag parent u)
    (havoid : ∀ y ∈ C.cap,
      E.data.width ≤ |⟪(u : E3), y⟫_ℝ - E.cutHeight|) :
    ∀ i : Fin 2, Disjoint C.cap (E.newCap i).cap := by
  intro i
  obtain ⟨_hdelta, _hc, hck, hkw, _hl, _hlM⟩ := E.parameter_bounds
  obtain ⟨_hprofile, _htube, hcut, hremoval, _hscale, _hsign⟩ := E.newCap_spec i
  apply C.cap_disjoint_of_height_avoidance (E.newCap i) E.data.width
  · rw [hremoval]
    exact hck.trans hkw
  · intro y hy
    rw [hcut]
    exact havoid y hy


theorem exists_inherited_cap_family
    {parent : UnitTwoSphere × ℝ → E3} {u : UnitTwoSphere}
    (E : RegularSurgeryEvent parent u) (n : ℕ)
    (C : Fin n → SurgeryCapTag parent u)
    (havoid : ∀ a : Fin n, ∀ y ∈ (C a).cap,
      E.data.width ≤ |⟪(u : E3), y⟫_ℝ - E.cutHeight|)
    (hdisjoint : Pairwise (fun a b : Fin n => Disjoint (C a).cap (C b).cap)) :
    ∃ i : Fin n → Fin 2,
      ∃ inherited : (a : Fin n) → SurgeryCapTag (E.child (i a)) u,
        (∀ a : Fin n,
          (C a).sourceCap ⊆
            (![E.data.sourceDiscs.positive, E.data.sourceDiscs.negative] (i a)) ''
              closedBall (0 : E2) E.radius ∧
          (∀ j : Fin 2, (C a).sourceCap ⊆
            (![E.data.sourceDiscs.positive, E.data.sourceDiscs.negative] j) ''
              closedBall (0 : E2) E.radius → j = i a) ∧
          (inherited a).profile = (C a).profile ∧
          (inherited a).tube = (C a).tube ∧
          (inherited a).cutHeight = (C a).cutHeight ∧
          (inherited a).removal = (C a).removal ∧
          (inherited a).scale = (C a).scale ∧
          (inherited a).sign = (C a).sign ∧
          (inherited a).sourceChart =
            (C a).sourceChart.trans (E.retainedChart (i a)).symm ∧
          (inherited a).flatChart =
            (C a).flatChart.trans (E.retainedChart (i a)).symm ∧
          (inherited a).beta = (C a).beta * E.retainedTime (i a) ∧
          (inherited a).overlapWidth ≤ (C a).overlapWidth ∧
          (inherited a).collarWidth =
            min 1 ((C a).collarWidth / (|E.retainedTime (i a)| + 1)) ∧
          (inherited a).cap = (C a).cap ∧
          (inherited a).seam = (C a).seam) ∧
        Pairwise (fun a b : Fin n =>
          Disjoint (inherited a).cap (inherited b).cap) ∧
        (∀ (a : Fin n) (j : Fin 2),
          Disjoint (inherited a).cap (E.newCap j).cap) ∧
        Disjoint (E.newCap 0).cap (E.newCap 1).cap := by
  classical
  choose i inherited hplace hunique hprofile htube hcut hremoval hscale hsign
    hsource hflat hbeta hoverlap hwidth hcap hseam using
      fun a : Fin n => E.exists_inherited_cap (C a) (havoid a)
  refine ⟨i, inherited, fun a => ⟨hplace a, hunique a, hprofile a, htube a,
    hcut a, hremoval a, hscale a, hsign a, hsource a, hflat a, hbeta a,
    hoverlap a, hwidth a, hcap a, hseam a⟩, ?_, ?_, ?_⟩
  · intro a b hab
    rw [hcap a, hcap b]
    exact hdisjoint hab
  · intro a j
    rw [hcap a]
    exact E.inherited_cap_disjoint_new (C a) (havoid a) j
  · obtain ⟨_hparent, _hannulus, _hcores, _hchild, _hseams, hchildren⟩ :=
      E.region_identities
    have hsub (j : Fin 2) : (E.newCap j).cap ⊆
        E.child j '' (univ ×ˢ ({0} : Set ℝ)) := by
      rintro y ⟨q, _hq, rfl⟩
      exact ⟨(q, 0), ⟨mem_univ _, rfl⟩, rfl⟩
    exact hchildren.mono (hsub 0) (hsub 1)

end PoincareConjecture.M25.Topology3D.RegularSurgeryEvent
