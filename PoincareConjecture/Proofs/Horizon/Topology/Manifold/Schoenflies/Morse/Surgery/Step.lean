import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Surgery.RegularLevelTwoSided
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Surgery.ComponentCount

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S1 := sphere (0 : E2) 1
private abbrev S2 := sphere (0 : E3) 1
local notation "Iprod" => ModelWithCorners.prod (𝓡 1) 𝓘(Real, Real)

structure SphereSurgeryStep (f : S2 → E3) (v : E3) (c R : Real) where
  original_embedding : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ f
  unit_v : ‖v‖ = 1
  p : S2
  center_height : inner Real v (f p) = c
  D : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞
  height_preserving : ∀ x, inner Real v (D x) = inner Real v x
  fixed_plane : ∀ x, inner Real v x = c → D x = x
  K : Set E3
  compact_K : IsCompact K
  support_subset : K ⊆ {x | |inner Real v x - c| ≤ R}
  eq_self_off : ∀ x ∉ K, D x = x
  prepared_embedding :
    _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ (fun p => D (f p))
  ε : Real
  ε_pos : 0 < ε
  ε_lt_R : ε < R
  T : OpenPartialHomeomorph (S1 × Real) S2
  tube_source : T.source = univ ×ˢ Ioo (-ε) ε
  tube_smooth : ContMDiffOn Iprod (𝓡 2) ∞ T T.source
  tube_symm_smooth : ContMDiffOn (𝓡 2) Iprod ∞ T.symm T.target
  center_range : range (fun q : S1 => T (q, 0)) =
    connectedComponentIn ((fun p => inner Real v (f p)) ⁻¹' {c}) p
  γ : S1 → Hemisphere.Plane v
  circle_embedding :
    _root_.Manifold.IsSmoothEmbedding (𝓡 1) 𝓘(Real, Hemisphere.Plane v) ∞ γ
  cylinder : ∀ q t, t ∈ Ioo (-ε) ε →
    D (f (T (q, t))) = (c + t) • v + (γ q : E3)
  A : Diffeomorph 𝓘(Real, Hemisphere.Plane v) 𝓘(Real, Hemisphere.Plane v)
    (Hemisphere.Plane v) (Hemisphere.Plane v) ∞
  circle_image : A '' sphere (0 : Hemisphere.Plane v) 1 = range γ
  disk_intersection :
    ((fun x : Hemisphere.Plane v => c • v + (A x : E3)) '' closedBall 0 1) ∩
      range (fun p => D (f p)) = (fun p => D (f p)) '' range (fun q : S1 => T (q, 0))
  a : Real
  a_pos : 0 < a
  a_lt_quarter_ε : a < ε / 4
  a_lt_quarter_R : a < R / 4
  s : Real
  s_pos : 0 < s
  s_lt_eighth_a : s < a / 8
  eMinus : OpenPartialHomeomorph E2 S2
  ePlus : OpenPartialHomeomorph E2 S2
  eMinus_source : closedBall 0 1 ⊆ eMinus.source
  ePlus_source : closedBall 0 1 ⊆ ePlus.source
  eMinus_smooth : ContMDiffOn (𝓡 2) (𝓡 2) ∞ eMinus eMinus.source
  eMinus_symm_smooth : ContMDiffOn (𝓡 2) (𝓡 2) ∞ eMinus.symm eMinus.target
  ePlus_smooth : ContMDiffOn (𝓡 2) (𝓡 2) ∞ ePlus ePlus.source
  ePlus_symm_smooth : ContMDiffOn (𝓡 2) (𝓡 2) ∞ ePlus.symm ePlus.target
  retained_disjoint : Disjoint (eMinus '' closedBall 0 1) (ePlus '' closedBall 0 1)
  eMinus_boundary : eMinus '' sphere (0 : E2) 1 = range (fun q : S1 => T (q, -a))
  ePlus_boundary : ePlus '' sphere (0 : E2) 1 = range (fun q : S1 => T (q, a))
  disk_slab_cover : eMinus '' closedBall 0 1 ∪ T '' (univ ×ˢ Icc (-a) a) ∪
    ePlus '' closedBall 0 1 = univ
  slab_eq : T '' (univ ×ˢ Icc (-a) a) =
    (eMinus '' ball 0 1 ∪ ePlus '' ball 0 1)ᶜ
  dMinus : OpenPartialHomeomorph E2 S2
  dPlus : OpenPartialHomeomorph E2 S2
  dMinus_source : closedBall 0 1 ⊆ dMinus.source
  dPlus_source : closedBall 0 1 ⊆ dPlus.source
  dMinus_smooth : ContMDiffOn (𝓡 2) (𝓡 2) ∞ dMinus dMinus.source
  dMinus_symm_smooth : ContMDiffOn (𝓡 2) (𝓡 2) ∞ dMinus.symm dMinus.target
  dPlus_smooth : ContMDiffOn (𝓡 2) (𝓡 2) ∞ dPlus dPlus.source
  dPlus_symm_smooth : ContMDiffOn (𝓡 2) (𝓡 2) ∞ dPlus.symm dPlus.target
  dMinus_closed : dMinus '' closedBall 0 1 = (eMinus '' ball 0 1)ᶜ
  dMinus_open : dMinus '' ball 0 1 = (eMinus '' closedBall 0 1)ᶜ
  dPlus_closed : dPlus '' closedBall 0 1 = (ePlus '' ball 0 1)ᶜ
  dPlus_open : dPlus '' ball 0 1 = (ePlus '' closedBall 0 1)ᶜ
  gMinus : E2 → E3
  gPlus : E2 → E3
  gMinus_smooth : ContDiff Real ∞ gMinus
  gPlus_smooth : ContDiff Real ∞ gPlus
  gMinus_injective : Injective gMinus
  gPlus_injective : Injective gPlus
  gMinus_deriv_injective : ∀ x, Injective (fderiv Real gMinus x)
  gPlus_deriv_injective : ∀ x, Injective (fderiv Real gPlus x)
  gMinus_width : ∀ x, |inner Real v (gMinus x) - (c - a)| < a / 2
  gPlus_width : ∀ x, |inner Real v (gPlus x) - (c + a)| < a / 2
  gMinus_range : gMinus '' closedBall (0 : E2) 1 =
    Poincare.Geometry.Euclidean.liftPlaneDiffeomorph unit_v (c - a) s s_pos.ne' A ''
      ((fun p : S2 => boundedCylinderRadius v p • (p : E3)) ''
        {p : S2 | 0 ≤ inner Real v (p : E3)})
  gPlus_range : gPlus '' closedBall (0 : E2) 1 =
    Poincare.Geometry.Euclidean.liftPlaneDiffeomorph unit_v (c + a) (-s)
      (neg_ne_zero.mpr s_pos.ne') A ''
      ((fun p : S2 => boundedCylinderRadius v p • (p : E3)) ''
        {p : S2 | 0 ≤ inner Real v (p : E3)})
  fMinus : S2 → E3
  fPlus : S2 → E3
  fMinus_embedding : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ fMinus
  fPlus_embedding : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ fPlus
  children_disjoint : Disjoint (range fMinus) (range fPlus)
  capMinus_eq : ∀ x ∈ closedBall 0 1, fMinus (dMinus x) = gMinus x
  capPlus_eq : ∀ x ∈ closedBall 0 1, fPlus (dPlus x) = gPlus x
  retainedMinus_eq : ∀ y ∈ eMinus '' closedBall 0 1, fMinus y = D (f y)
  retainedPlus_eq : ∀ y ∈ ePlus '' closedBall 0 1, fPlus y = D (f y)
  fMinus_range : range fMinus = gMinus '' closedBall 0 1 ∪
    (fun p => D (f p)) '' (eMinus '' closedBall 0 1)
  fPlus_range : range fPlus = gPlus '' closedBall 0 1 ∪
    (fun p => D (f p)) '' (ePlus '' closedBall 0 1)
  parallel_disk_intersection : ∀ t ∈ Icc (-(2 * a)) (2 * a),
    ((fun x : Hemisphere.Plane v => (c + t) • v + (A x : E3)) '' closedBall 0 1) ∩
      range (fun p => D (f p)) = (fun p => D (f p)) '' range (fun q : S1 => T (q, t))

theorem nonempty_sphereSurgeryStep_of_smooth
    {f : S2 → E3} (hf : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ f)
    {h : S2 → Real} (hh : ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ h)
    {v : E3} (hv : ‖v‖ = 1) (hheight : ∀ p, inner Real v (f p) = h p)
    (c : Real) (hc : ∀ p, h p = c → mfderiv (𝓡 2) 𝓘(Real, Real) h p ≠ 0)
    (hne : (h ⁻¹' {c}).Nonempty) {R : Real} (hR : 0 < R) :
    Nonempty (SphereSurgeryStep f v c R) := by
  obtain ⟨p, hp, D, hDh, hDp, ⟨K, hK, hKR, hDK⟩, hDf,
    ε, hε, hεR, T, hTs, hT, hTi, hcenter, γ, hγ, hcylinder, A, hA, hintersection,
    a, ha, haε, haR, s, hs, hsa, eM, eP, heMs, hePs, heM, heMi, heP, hePi,
    heDis, heMb, hePb, heCover, heSlab, dM, dP, hdMs, hdPs, hdM, hdMi, hdP, hdPi,
    hdMc, hdMb, hdPc, hdPb, gM, gP, hgM, hgP, hgMinj, hgPinj, hgMder, hgPder,
    hgMw, hgPw, hgMr, hgPr, fM, fP, hfM, hfP, hfDis, hcapM, hcapP,
    hoffM, hoffP, hrangeM, hrangeP, hparallel⟩ :=
    exists_regular_level_two_sided_surgery_of_smooth hf hh hv hheight c hc hne hR
  refine ⟨{
    original_embedding := hf
    unit_v := hv
    p := p
    center_height := (hheight p).trans hp
    D := D
    height_preserving := hDh
    fixed_plane := hDp
    K := K
    compact_K := hK
    support_subset := hKR
    eq_self_off := hDK
    prepared_embedding := hDf
    ε := ε
    ε_pos := hε
    ε_lt_R := hεR
    T := T
    tube_source := hTs
    tube_smooth := hT
    tube_symm_smooth := hTi
    center_range := ?_
    γ := γ
    circle_embedding := hγ
    cylinder := hcylinder
    A := A
    circle_image := hA
    disk_intersection := hintersection
    a := a
    a_pos := ha
    a_lt_quarter_ε := haε
    a_lt_quarter_R := haR
    s := s
    s_pos := hs
    s_lt_eighth_a := hsa
    eMinus := eM
    ePlus := eP
    eMinus_source := heMs
    ePlus_source := hePs
    eMinus_smooth := heM
    eMinus_symm_smooth := heMi
    ePlus_smooth := heP
    ePlus_symm_smooth := hePi
    retained_disjoint := heDis
    eMinus_boundary := heMb
    ePlus_boundary := hePb
    disk_slab_cover := heCover
    slab_eq := heSlab
    dMinus := dM
    dPlus := dP
    dMinus_source := hdMs
    dPlus_source := hdPs
    dMinus_smooth := hdM
    dMinus_symm_smooth := hdMi
    dPlus_smooth := hdP
    dPlus_symm_smooth := hdPi
    dMinus_closed := hdMc
    dMinus_open := hdMb
    dPlus_closed := hdPc
    dPlus_open := hdPb
    gMinus := gM
    gPlus := gP
    gMinus_smooth := hgM
    gPlus_smooth := hgP
    gMinus_injective := hgMinj
    gPlus_injective := hgPinj
    gMinus_deriv_injective := hgMder
    gPlus_deriv_injective := hgPder
    gMinus_width := hgMw
    gPlus_width := hgPw
    gMinus_range := hgMr
    gPlus_range := hgPr
    fMinus := fM
    fPlus := fP
    fMinus_embedding := hfM
    fPlus_embedding := hfP
    children_disjoint := hfDis
    capMinus_eq := hcapM
    capPlus_eq := hcapP
    retainedMinus_eq := hoffM
    retainedPlus_eq := hoffP
    fMinus_range := hrangeM
    fPlus_range := hrangeP
    parallel_disk_intersection := hparallel }⟩
  simpa only [hheight] using hcenter

namespace SphereSurgeryStep

variable {f : S2 → E3} {v : E3} {c R : Real} (S : SphereSurgeryStep f v c R)

theorem prepared_height_eq : (fun p => inner Real v (S.D (f p))) =
    (fun p => inner Real v (f p)) := funext fun p => S.height_preserving (f p)

theorem tube_height (q : S1) (t : Real) (ht : t ∈ Ioo (-S.ε) S.ε) :
    inner Real v (f (S.T (q, t))) = c + t := by
  rw [← S.height_preserving, S.cylinder q t ht]
  simp [inner_add_right, inner_smul_right, S.unit_v,
    Submodule.mem_orthogonal_singleton_iff_inner_right.mp (S.γ q).property]

theorem capMinus_avoids (x : E2) : inner Real v (S.gMinus x) ≠ c := by
  intro heq
  have hb := (abs_lt.mp (S.gMinus_width x)).2
  rw [heq] at hb
  linarith [S.a_pos]

theorem capPlus_avoids (x : E2) : inner Real v (S.gPlus x) ≠ c := by
  intro heq
  have hb := (abs_lt.mp (S.gPlus_width x)).1
  rw [heq] at hb
  linarith [S.a_pos]

theorem central_regular
    (hc : ∀ p, inner Real v (f p) = c →
      mfderiv (𝓡 2) 𝓘(Real, Real) (fun q => inner Real v (f q)) p ≠ 0) :
    (∀ p, inner Real v (S.fMinus p) = c →
      mfderiv (𝓡 2) 𝓘(Real, Real) (fun q => inner Real v (S.fMinus q)) p ≠ 0) ∧
    (∀ p, inner Real v (S.fPlus p) = c →
      mfderiv (𝓡 2) 𝓘(Real, Real) (fun q => inner Real v (S.fPlus q)) p ≠ 0) := by
  have hcD : ∀ p, inner Real v (S.D (f p)) = c →
      mfderiv (𝓡 2) 𝓘(Real, Real) (fun q => inner Real v (S.D (f q))) p ≠ 0 := by
    rw [S.prepared_height_eq]
    simpa only [S.height_preserving] using hc
  exact ⟨regular_level_of_disk_splicing (fun p => S.D (f p)) S.fMinus v c
      S.eMinus S.dMinus S.eMinus_source S.dMinus_closed S.gMinus
      S.capMinus_eq S.retainedMinus_eq (fun x _ => S.capMinus_avoids x) hcD,
    regular_level_of_disk_splicing (fun p => S.D (f p)) S.fPlus v c
      S.ePlus S.dPlus S.ePlus_source S.dPlus_closed S.gPlus
      S.capPlus_eq S.retainedPlus_eq (fun x _ => S.capPlus_avoids x) hcD⟩

theorem central_card_drop
    [Finite (ConnectedComponents ((fun p => inner Real v (f p)) ⁻¹' {c}))] :
    let Lminus := (fun p => inner Real v (S.fMinus p)) ⁻¹' {c}
    let Lplus := (fun p => inner Real v (S.fPlus p)) ⁻¹' {c}
    let L := (fun p => inner Real v (f p)) ⁻¹' {c}
    Finite (ConnectedComponents Lminus) ∧ Finite (ConnectedComponents Lplus) ∧
      Nat.card (ConnectedComponents Lminus) + Nat.card (ConnectedComponents Lplus) + 1 =
        Nat.card (ConnectedComponents L) ∧
      Nat.card (ConnectedComponents Lminus) + Nat.card (ConnectedComponents Lplus) <
        Nat.card (ConnectedComponents L) := by
  let : Finite (ConnectedComponents ((fun p => inner Real v (S.D (f p))) ⁻¹' {c})) := by
    rw [S.prepared_height_eq]
    infer_instance
  have hheight (q : S1) (t : Real) (ht : t ∈ Ioo (-S.ε) S.ε) :
      inner Real v (S.D (f (S.T (q, t)))) = c + t := by
    rw [S.height_preserving]
    exact S.tube_height q t ht
  have hp : inner Real v (S.D (f S.p)) = c := by
    rw [S.height_preserving]
    exact S.center_height
  have hcenter : range (fun q : S1 => S.T (q, 0)) =
      connectedComponentIn ((fun p => inner Real v (S.D (f p))) ⁻¹' {c}) S.p := by
    simpa only [S.prepared_height_eq] using S.center_range
  have haε : S.a < S.ε := by linarith [S.a_lt_quarter_ε, S.ε_pos]
  have hresult :=
    card_level_components_of_parallel_disk_splicing (fun p => S.D (f p)) S.fMinus S.fPlus v
      S.a_pos haε S.T S.tube_source hheight
      S.p hp hcenter S.eMinus S.ePlus S.dMinus S.dPlus S.eMinus_source S.ePlus_source
      S.retained_disjoint S.slab_eq S.dMinus_closed S.dPlus_closed S.gMinus S.gPlus
      S.capMinus_eq S.capPlus_eq S.retainedMinus_eq S.retainedPlus_eq
      (fun x _ => S.capMinus_avoids x) (fun x _ => S.capPlus_avoids x)
  dsimp only at hresult
  rw [S.prepared_height_eq] at hresult
  exact hresult

end SphereSurgeryStep

end Poincare.Manifold.Schoenflies
