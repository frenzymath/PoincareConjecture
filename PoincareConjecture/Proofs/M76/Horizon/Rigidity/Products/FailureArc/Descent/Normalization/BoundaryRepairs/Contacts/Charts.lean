import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Normalization.BoundaryRepairs.Contacts.RimVertices
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Normalization.BoundaryRepairs.Contacts.Coordinates
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.EmptyInteriorFaceDimension



set_option autoImplicit false
open Set Metric Geometry Geometry.SimplicialComplex Topology unitInterval PLAnnularStrip

namespace Geometry.OriginalPLTower

local notation "P2" => (ℝ × ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)
local notation "Ann" => squareAnnulus 8 1
local notation "Rim" => Set.ofPred (fun z : P2 => depth 8 z = -1 ∨ depth 8 z = 1)

variable {U M ι : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [TopologicalSpace M]
  {e : ι → OpenPartialHomeomorph M V3} {S : SimplicialComplex ℝ U}
  {f : U → M} {r : M → ℝ} {C : Set M} {s t : Stage e S f r C}
  {step : Step s t} {K₀ A₀ : SimplicialComplex ℝ P2}
  {j : P2 → t.Carrier} {R Fmark : Set M}

set_option maxHeartbeats 800000 in
theorem MarkedSurfacePositionData.exists_annulus_boundary_crossed_charts
    (D : MarkedSurfacePositionData step K₀ A₀ j R Fmark)
    (hAnn : D.K.space = Ann) (hRim : A₀.space = Rim)
    {a b : Ann} {W : Set s.Carrier} {ε : ℝ}
    (N : PlanarAnnulusBoundaryMotion step D.endpoint R Fmark a b W ε)
    (hseparate : W ∩ ((fun z : P2 × P2 => D.projected z.1) '' D.repairPairs) ⊆
      {D.projected a}) :
    ∃ B K : SimplicialComplex ℝ V3,
      B.faces.Finite ∧ K.faces.Finite ∧ K ≤ B ∧
      B.space = (N.window.right.trans N.chart) ''
        (((N.ambient 1) ∘ D.endpoint) '' Ann ∩ (N.window.right.trans N.chart).source) ∩
          N.support.space ∧
      K.space = (N.window.right.trans N.chart) ''
        (((N.ambient 1) ∘ D.endpoint) '' Rim ∩ (N.window.right.trans N.chart).source) ∩
          N.support.space ∧
      K.space = B.space ∩ {z | (N.coordinates z).1.1 = 0} ∧
      ∀ z ∈ K.space, z ∈ interior N.support.space → (N.coordinates z).2 = 0 →
        ∀ O : Set s.Carrier, IsOpen O → N.chart.symm z ∈ O →
          ∃ T : OpenPartialHomeomorph s.Carrier V3,
            N.chart.symm z ∈ T.source ∧ T (N.chart.symm z) = 0 ∧
            T.source ⊆ O ∩ N.chart.source ∧
            (∀ k, (s.charts k).symm.trans T ∈ piecewiseAffineGroupoid V3) ∧
            (step.projection ∘ step.inclusion) ⁻¹' T.source =
              (N.window.left.source ∩ (step.projection ∘ step.inclusion) ⁻¹' T.source) ∪
                (N.window.right.source ∩ (step.projection ∘ step.inclusion) ⁻¹' T.source) ∧
            (∀ y ∈ T.source, y ∈ s.projection ⁻¹' R ↔ 0 ≤ (N.coordinates (T y)).2) ∧
            (∀ y ∈ T.source, y ∈ frontier (s.projection ⁻¹' R) ↔ (N.coordinates (T y)).2 = 0) ∧
            (∀ y ∈ T.source, y ∈ (step.projection ∘ step.inclusion) ''
              (((N.ambient 1) ∘ D.endpoint) '' Ann ∩ N.window.left.source) ↔
                0 ≤ (N.coordinates (T y)).2 ∧ (N.coordinates (T y)).1.1 = 0) ∧
            ∀ y ∈ T.source, y ∈ (step.projection ∘ step.inclusion) ''
              (((N.ambient 1) ∘ D.endpoint) '' Ann ∩ N.window.right.source) ↔
                0 ≤ (N.coordinates (T y)).2 ∧ (N.coordinates (T y)).1.2 = 0 := by
  classical
  have hj : PolyhedralPLInCharts t.charts D.endpoint Ann :=
    hAnn ▸ (D.states D.length).original_PL
  obtain ⟨B, K, hB, hK, hKB, _, hvertices, hBs, hKs, hKzero, hqB, hqi,
    hqAnn, hqrim, hcofaces⟩ := N.exists_moved_boundary_cofaces hj
  have hzero := D.moved_annulus_boundary_vertices_nonzero hAnn hRim N hseparate K hvertices
  let q := N.parameter ∘ (N.motion.map 1).symm
  have hqK : K.AffineOnFaces q := fun face hf => hqB face (hKB hf)
  have hqKi : InjOn q K.space := hqi.mono (space_subset_of_le hKB)
  have hqKRim : q '' K.space ⊆ Rim := by
    rintro _ ⟨x, hx, rfl⟩
    exact (hqrim x (space_subset_of_le hKB hx)).mp hx
  have hRimFrontier : Rim = frontier Ann := by
    ext x
    exact (PoincareConjecture.M76.Dehn.Annuli.mem_frontier_planar_annulus_iff x).symm
  have hKcard (face : Finset V3) (hf : face ∈ K.faces) : face.card ≤ 2 := by
    have hint : interior (q '' K.space) = ∅ := by
      apply Set.subset_empty_iff.mp
      have h := interior_mono hqKRim
      rwa [hRimFrontier, interior_frontier
        PoincareConjecture.M76.Dehn.Annuli.isCompact_planar_annulus.isClosed] at h
    simpa using hqK.face_card_le_of_injOn_of_empty_interior hqKi hint hf
  let p := step.projection ∘ step.inclusion
  let Q := N.chart
  let w := N.window
  let c := N.coordinates
  let moved := (N.ambient 1) ∘ D.endpoint
  have hleftimage : moved '' Ann ∩ w.left.source = D.endpoint '' Ann ∩ w.left.source := by
    ext x
    constructor
    · rintro ⟨⟨y, hy, hyx⟩, hx⟩
      have he : N.ambient 1 (D.endpoint y) = x := hyx
      have hold : D.endpoint y = x := (N.ambient 1).injective (he.trans (N.left_fixed 1 hx).symm)
      exact ⟨⟨y, hy, hold⟩, hx⟩
    · rintro ⟨⟨y, hy, rfl⟩, hx⟩
      exact ⟨⟨y, hy, N.left_fixed 1 hx⟩, hx⟩
  have hnewplane (y : s.Carrier) (hy : y ∈ Q.source) :
      y ∈ p '' (moved '' Ann ∩ w.left.source) ↔ 0 ≤ (c (Q y)).1.1 ∧ (c (Q y)).2 = 0 := by
    rw [hleftimage]
    exact N.left_halfplane y hy
  have hBpositive (z : V3) (hz : z ∈ B.space) : 0 ≤ (c z).1.1 := by
    obtain ⟨v, hv, rfl⟩ := hBs.subset hz
    rw [N.height]
    obtain ⟨⟨u, ⟨⟨x, hx, hxu⟩, huT⟩, huv⟩, _⟩ := N.source_space.subset hv
    have huQ : p u ∈ Q.source := by
      have h : w.right u ∈ Q.source := huT.2
      rw [congrFun w.right_eq u] at h
      exact h
    have huR : p u ∈ s.projection ⁻¹' R := by
      have h := D.projected_region (hAnn.symm.subset hx)
      change p (D.endpoint x) ∈ s.projection ⁻¹' R at h
      exact hxu ▸ h
    have hh := (N.lower_region (p u) huQ).mp huR
    change Q (w.right u) = v at huv
    rw [congrFun w.right_eq u] at huv
    exact huv ▸ hh
  have hBs' : B.space = (w.right.trans Q) '' (moved '' Ann ∩ (w.right.trans Q).source) ∩
      N.support.space := hBs.trans (N.source_image 1).symm
  have hKs' : K.space = (w.right.trans Q) '' (moved '' Rim ∩ (w.right.trans Q).source) ∩
      N.support.space := hKs.trans (N.boundary_image 1).symm
  refine ⟨B, K, hB, hK, hKB, hBs', hKs', hKzero, ?_⟩
  intro z hzK hzJ hz0 O hO hzO
  let V := Q.target ∩ Q.symm ⁻¹' O
  have hV : IsOpen V := Q.symm.isOpen_inter_preimage hO
  have hzV : z ∈ V := ⟨N.support_target (interior_subset hzJ), hzO⟩
  obtain ⟨F, N₀, hN₀, hzN₀, hNsub, hFzero, hFheight, hFell, hlocal⟩ :=
    exists_boundary_carrier_affine_coordinates N.support B K c hK hKB hKcard hKzero
      hzero hBpositive hcofaces hzK hzJ hz0 V hV hzV
  let perm : C3 ≃ₗ[ℝ] C3 :=
    { toFun := fun x => ((x.2, x.1.1), x.1.2)
      invFun := fun x => ((x.1.2, x.2), x.1.1)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let coord := (F.trans perm.toAffineEquiv.toContinuousAffineEquiv).trans
    c.symm.toLinearEquiv.toAffineEquiv.toContinuousAffineEquiv
  let T := Q.trans (coord.toHomeomorph.toOpenPartialHomeomorph.restrOpen N₀ hN₀)
  have hzT : Q.symm z ∈ T.source := by
    refine ⟨Q.map_target (N.support_target (interior_subset hzJ)), mem_univ _, ?_⟩
    change Q (Q.symm z) ∈ N₀
    rw [Q.right_inv (N.support_target (interior_subset hzJ))]
    exact hzN₀
  have hvalue (y : s.Carrier) : c (T y) =
      (((c (Q y)).2, (F (Q y)).1.1), (c (Q y)).1.1) := by
    change c (c.symm (perm (F (Q y)))) = _
    rw [c.apply_symm_apply]
    change (((F (Q y)).2, (F (Q y)).1.1), (F (Q y)).1.2) = _
    rw [hFell, hFheight]
  have hsource (y : s.Carrier) (hy : y ∈ T.source) : y ∈ O ∩ Q.source := by
    have hyO := (hNsub hy.2.2).1.2
    change Q.symm (Q y) ∈ O at hyO
    rw [Q.left_inv hy.1] at hyO
    exact ⟨hyO, hy.1⟩
  have hTPL (k : s.Index) : (s.charts k).symm.trans T ∈ piecewiseAffineGroupoid V3 := by
    apply (mem_piecewiseAffineGroupoid_iff_forward _).mpr
    exact ((locallyPiecewiseAffineOn_affine coord.toContinuousAffineMap isOpen_univ).comp
      (N.lower_PL k).1).mono ((s.charts k).symm.trans T).open_source
        (fun x hx => ⟨⟨hx.1, hx.2.1⟩, mem_univ _⟩)
  refine ⟨T, hzT, ?_, hsource, hTPL, ?_, ?_, ?_, ?_, ?_⟩
  · change c.symm (perm (F (Q (Q.symm z)))) = 0
    rw [Q.right_inv (N.support_target (interior_subset hzJ)), hFzero, map_zero, map_zero]
  · ext x
    constructor
    · intro hx
      rcases w.whole_preimage.subset ((N.chart_inside hx.1).2) with hl | hr
      · exact Or.inl ⟨hl, hx⟩
      · exact Or.inr ⟨hr, hx⟩
    · exact fun hx => hx.elim And.right And.right
  · intro y hy
    rw [hvalue]
    exact N.lower_region y hy.1
  · intro y hy
    rw [hvalue]
    exact N.lower_frontier y hy.1
  · intro y hy
    rw [hvalue]
    exact hnewplane y hy.1
  · intro y hy
    have hyJ := interior_subset (hNsub hy.2.2).2
    have hright : y ∈ p '' (moved '' Ann ∩ w.right.source) ↔ Q y ∈ B.space := by
      rw [hBs']
      constructor
      · rintro ⟨x, ⟨hxD, hxw⟩, hxy⟩
        refine ⟨⟨x, ⟨hxD, hxw, ?_⟩, ?_⟩, hyJ⟩
        · change w.right x ∈ Q.source
          rw [congrFun w.right_eq x]
          change p x ∈ Q.source
          rw [hxy]
          exact hy.1
        · change Q (w.right x) = Q y
          rw [congrFun w.right_eq x]
          exact congrArg Q hxy
      · rintro ⟨⟨x, ⟨hxD, hxT⟩, hxy⟩, _⟩
        refine ⟨x, ⟨hxD, hxT.1⟩, ?_⟩
        have hxQ : p x ∈ Q.source := by
          have h : w.right x ∈ Q.source := hxT.2
          rw [congrFun w.right_eq x] at h
          exact h
        apply Q.injOn hxQ hy.1
        change Q (w.right x) = Q y at hxy
        rw [congrFun w.right_eq x] at hxy
        exact hxy
    rw [hright, hvalue]
    exact hlocal (Q y) hy.2.2

end Geometry.OriginalPLTower
