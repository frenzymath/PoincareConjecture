import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Positive.Regions.Model
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Tube.Gluing.Coordinates.SliceShift











set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.NoncompactKappa.Positive.SoulNeckRegion

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
  {K : AncientKappaSolution 3 M}
  {S : RiemannianMetric.PointSoulData (K.flow.metric 0)} {epsilon D R : ℝ}
  (G : SoulNeckRegion K S epsilon D R)



theorem exists_closed_side_expansion (Q : EpsilonNeck (K.flow.metric 0))
    (hsphere : Q.central_sphere = G.neck.terminal_neck.central_sphere)
    (hheight : ∀ y ∈ Q.carrier,
      y ∈ closure G.inside ↔ (Q.coordinate_inverse y).2 ≤ 0)
    {b : ℝ} (hb : 0 < b) (hbQ : b < Q.epsilon⁻¹) :
    ∃ F : Diffeomorph (𝓡 3) (𝓡 3) M M ∞,
      (∀ x, x ∉ Q.carrier → F x = x) ∧
      (∀ x ∈ Q.carrier,
        x ∈ F '' closure G.inside ↔ (Q.coordinate_inverse x).2 ≤ b) ∧
      F '' G.neck.terminal_neck.central_sphere =
        range (fun q : UnitTwoSphere => Q.coordinate_map (q, b)) := by
  have hL : 0 < Q.epsilon⁻¹ := inv_pos.mpr Q.epsilon_pos
  obtain ⟨rho, F, hrho, hfixed, hlocal, hsublevel⟩ :=
    Q.exists_smooth_slice_shift ⟨neg_neg_of_pos hL, hL⟩
      ⟨by linarith, hbQ⟩ hb
  have hmem (x : M) : F x ∈ Q.carrier ↔ x ∈ Q.carrier :=
    F.mem_iff_of_fixed_compl subset_rfl hfixed x
  have hclosed (x : M) (hx : x ∈ Q.carrier) :
      x ∈ F '' closure G.inside ↔ (Q.coordinate_inverse x).2 ≤ b := by
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hyQ : y ∈ Q.carrier := (hmem y).mp hx
      have hy0 := (hheight y hyQ).mp hy
      have hFy : F y ∈ F '' {x | x ∈ Q.carrier ∧ (Q.coordinate_inverse x).2 ≤ 0} :=
        ⟨y, ⟨hyQ, hy0⟩, rfl⟩
      exact (hsublevel ▸ hFy).2
    · intro hxb
      have hximage : x ∈ F '' {y | y ∈ Q.carrier ∧ (Q.coordinate_inverse y).2 ≤ 0} :=
        hsublevel.symm ▸ ⟨hx, hxb⟩
      obtain ⟨y, hy, rfl⟩ := hximage
      exact ⟨y, (hheight y hy.1).mpr hy.2, rfl⟩
  refine ⟨F, hfixed, hclosed, ?_⟩
  rw [← hsphere, ← Q.centralSphere_range]
  ext x
  constructor
  · rintro ⟨_, ⟨q, rfl⟩, rfl⟩
    refine ⟨q, ?_⟩
    symm
    simpa only [sub_zero, zero_add] using
      hlocal (q, 0) ⟨mem_univ _, neg_neg_of_pos hL, hL⟩ (by simpa using hrho)
  · rintro ⟨q, rfl⟩
    refine ⟨Q.coordinate_map (q, 0), mem_range_self q, ?_⟩
    simpa only [sub_zero, zero_add] using
      hlocal (q, 0) ⟨mem_univ _, neg_neg_of_pos hL, hL⟩ (by simpa using hrho)



theorem exists_side_expansion (Q : EpsilonNeck (K.flow.metric 0))
    (hsphere : Q.central_sphere = G.neck.terminal_neck.central_sphere)
    (hheight : ∀ y ∈ Q.carrier,
      y ∈ closure G.inside ↔ (Q.coordinate_inverse y).2 ≤ 0)
    {b : ℝ} (hb : 0 < b) (hbQ : b < Q.epsilon⁻¹) :
    ∃ F : Diffeomorph (𝓡 3) (𝓡 3) M M ∞,
      F '' G.inside = G.inside ∪ Q.region (-Q.epsilon⁻¹) b ∧
      closure G.inside ⊆ F '' G.inside ∧
      frontier (F '' G.inside) =
        range (fun q : UnitTwoSphere => Q.coordinate_map (q, b)) := by
  obtain ⟨F, hfixed, hclosed, hsphereF⟩ := G.exists_closed_side_expansion Q hsphere hheight hb hbQ
  have hfront : frontier (F '' G.inside) =
      range (fun q : UnitTwoSphere => Q.coordinate_map (q, b)) := by
    have h := F.toHomeomorph.image_frontier G.inside
    change F '' frontier G.inside = frontier (F '' G.inside) at h
    rw [G.inside_frontier] at h
    exact h.symm.trans hsphereF
  have hcl : closure (F '' G.inside) = F '' closure G.inside :=
    (F.toHomeomorph.image_closure G.inside).symm
  have hopen : IsOpen (F '' G.inside) := F.toHomeomorph.isOpenMap _ G.inside_open
  have hboundary (x : M) (hx : x ∈ Q.carrier) :
      x ∈ frontier (F '' G.inside) ↔ (Q.coordinate_inverse x).2 = b := by
    rw [hfront]
    constructor
    · rintro ⟨q, rfl⟩
      have hdom : (q, b) ∈ Q.cylinderDomain :=
        ⟨mem_univ _, by linarith [inv_pos.mpr Q.epsilon_pos], hbQ⟩
      rw [Q.coordinate_inverse_coordinate_map hdom]
    · intro heq
      refine ⟨(Q.coordinate_inverse x).1, ?_⟩
      rw [← heq]
      exact Q.coordinate_map_coordinate_inverse hx
  have hinside (x : M) (hx : x ∈ Q.carrier) :
      x ∈ F '' G.inside ↔ (Q.coordinate_inverse x).2 < b := by
    constructor
    · intro hi
      have hle := (hclosed x hx).mp (hcl ▸ subset_closure hi)
      refine lt_of_le_of_ne hle ?_
      intro heq
      have hf := (hboundary x hx).mpr heq
      exact (hopen.frontier_eq ▸ hf).2 hi
    · intro hlt
      have hc : x ∈ closure (F '' G.inside) := hcl.symm ▸ (hclosed x hx).mpr hlt.le
      by_contra hn
      have hf : x ∈ frontier (F '' G.inside) := hopen.frontier_eq.symm ▸ ⟨hc, hn⟩
      exact hlt.ne ((hboundary x hx).mp hf)
  have himage : F '' G.inside = G.inside ∪ Q.region (-Q.epsilon⁻¹) b := by
    ext x
    by_cases hx : x ∈ Q.carrier
    · constructor
      · intro hi
        exact Or.inr ⟨hx, (Q.coordinate_inverse_mem x hx).2.1, (hinside x hx).mp hi⟩
      · intro hi
        apply (hinside x hx).mpr
        rcases hi with hi | hi
        · exact ((hheight x hx).mp (subset_closure hi)).trans_lt hb
        · exact hi.2.2
    · constructor
      · rintro ⟨y, hy, heq⟩
        have hyx : y = x := F.injective (heq.trans (hfixed x hx).symm)
        exact Or.inl (hyx ▸ hy)
      · rintro (hi | hi)
        · exact ⟨x, hi, hfixed x hx⟩
        · exact (hx hi.1).elim
  refine ⟨F, himage, ?_, hfront⟩
  intro x hx
  by_cases hi : x ∈ G.inside
  · exact himage.symm ▸ Or.inl hi
  · have hfrontx : x ∈ G.neck.terminal_neck.central_sphere :=
      G.inside_frontier ▸ (G.inside_open.frontier_eq.symm ▸ ⟨hx, hi⟩)
    have hxQ := Q.central_sphere_subset (hsphere.symm ▸ hfrontx)
    apply (hinside x hxQ).mpr
    rw [((Q.mem_central_sphere_iff x).mp (hsphere.symm ▸ hfrontx)).2]
    exact hb



theorem nonempty_expanded_side_capModel (Q : EpsilonNeck (K.flow.metric 0))
    (hsphere : Q.central_sphere = G.neck.terminal_neck.central_sphere)
    (hheight : ∀ y ∈ Q.carrier,
      y ∈ closure G.inside ↔ (Q.coordinate_inverse y).2 ≤ 0)
    {b : ℝ} (hb : 0 < b) (hbQ : b < Q.epsilon⁻¹) (p : RealProjectiveThree) :
    Nonempty (CapModelEquivalence .euclidean p
      (G.inside ∪ Q.region (-Q.epsilon⁻¹) b)) := by
  obtain ⟨F, hF, _, _⟩ := G.exists_side_expansion Q hsphere hheight hb hbQ
  exact hF ▸ G.nonempty_capModel_image_inside F p

end PoincareConjecture.NoncompactKappa.Positive.SoulNeckRegion
