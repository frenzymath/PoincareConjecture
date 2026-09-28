import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Surfaces.GroupRank.OriginalComponent
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Coverings.Phase.SquareParametrization
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Surfaces.Cuts.OriginalOrientedSquareMap
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonStandardAtlasExistence








set_option autoImplicit false

open Set Geometry AbstractSimplicialComplex
open PreAbstractSimplicialComplex.ModTwoCochains

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) hamiltonZeroPeriodLattice

open Classical in
theorem PLDomain.exists_original_oriented_component_euler_zero
    {ι : Type*} (e : ι → OpenPartialHomeomorph X0 V3)
    (hcover : ∀ x, ∃ i, x ∈ (e i).source)
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    {N : Set X0} (he : PLDomain e N) (hN : IsCompact N)
    (x : X0) (hx : x ∈ frontier N)
    (hnt : Nontrivial (FundamentalGroup (connectedComponentIn (frontier N) x)
      ⟨x, mem_connectedComponentIn hx⟩))
    (hinj : Function.Injective (FundamentalGroup.map
      (⟨Subtype.val, continuous_subtype_val⟩ :
        C(connectedComponentIn (frontier N) x, X0)) ⟨x, mem_connectedComponentIn hx⟩)) :
    ∃ (s : Finset N) (phi : X0 → (s → ℝ × V3))
      (J : SimplicialComplex ℝ (s → ℝ × V3)) (g : (s → ℝ × V3) → X0)
      (H : J.space ≃ₜ connectedComponentIn (frontier N) x),
      Continuous phi ∧
      (∀ i, LocallyPiecewiseAffineOn (phi ∘ (e i).symm) (e i).target) ∧
      J.faces.Finite ∧ IsConnected J.space ∧ J.surfaceEulerCount = 0 ∧
      (∀ t ∈ J.faces, ∃ u ∈ J.faces, t ⊆ u ∧ u.card = 3) ∧
      (∀ t ∈ J.faces, t.card = 2 →
        {u : Finset (s → ℝ × V3) | u ∈ J.faces ∧ u.card = 3 ∧ t ⊆ u}.ncard = 2) ∧
      (∀ p ∈ J.vertices, IsConnected (J.faceLink {p}).space) ∧
      PolyhedralPLInCharts e g J.space ∧
      (∀ z : J.space, (H z : X0) = g z) ∧
      (∀ z ∈ J.space, phi (g z) = z) ∧
      ∃ (number : J.vertices ↪ ℕ)
        (sigma : Triangle J.vertexAbstractComplex.toPreAbstractSimplicialComplex → ZMod 2),
        ∀ t u : Triangle J.vertexAbstractComplex.toPreAbstractSimplicialComplex,
          t ≠ u → ∀ a : Edge J.vertexAbstractComplex.toPreAbstractSimplicialComplex,
          a.val ⊆ t.val → a.val ⊆ u.val →
          (sigma t + boundaryFaceParity number t.val a.val) +
            (sigma u + boundaryFaceParity number u.val a.val) = 1 := by
  obtain ⟨s, phi, J, g, H, hphi, hphiPL, hJ, hconn, hpure, hcofaces, hlinks,
    hgPL, hH, hinverse, number, sigma, hcancel⟩ :=
    he.exists_original_oriented_component e hcover hcompat hN x hx
  let b : connectedComponentIn (frontier N) x := ⟨x, mem_connectedComponentIn hx⟩
  obtain ⟨_, _, hnt', hinj'⟩ :=
    originalComponentGroups_at_original_basepoint g H hH b hnt hinj
  let : Nontrivial (FundamentalGroup J.space (H.symm b)) := hnt'
  let f := (hamiltonZeroAmbientIntegerMap
    (originalComponentAmbientMap g H hH (H.symm b))).comp
      (FundamentalGroup.map (originalComponentAmbientMap g H hH) (H.symm b))
  have hf : Function.Injective f :=
    (hamiltonZeroAmbientIntegerMap_injective _).comp hinj'
  have hzero := surfaceEulerCount_eq_zero_of_injective_integer_three_and_signs
    J hJ hpure hconn (by intro v hv; convert! hlinks v hv) hcofaces number sigma
      (by intro t u htu a hat hau; convert! hcancel t u htu a hat hau) (H.symm b) f hf
  exact ⟨s, phi, J, g, H, hphi, hphiPL, hJ, hconn, hzero, hpure, hcofaces, hlinks,
    hgPL, hH, hinverse, number, sigma, hcancel⟩

open Classical in


theorem PLDomain.exists_original_frontier_torus_square_model
    {ι : Type*} (e : ι → OpenPartialHomeomorph X0 V3)
    (hcover : ∀ x, ∃ i, x ∈ (e i).source)
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    {N : Set X0} (he : PLDomain e N) (hN : IsCompact N)
    (x : X0) (hx : x ∈ frontier N)
    (hnt : Nontrivial (FundamentalGroup (connectedComponentIn (frontier N) x)
      ⟨x, mem_connectedComponentIn hx⟩))
    (hinj : Function.Injective (FundamentalGroup.map
      (⟨Subtype.val, continuous_subtype_val⟩ :
        C(connectedComponentIn (frontier N) x, X0)) ⟨x, mem_connectedComponentIn hx⟩)) :
    ∃ (s : Finset N) (phi : X0 → (s → ℝ × V3))
      (J : SimplicialComplex ℝ (s → ℝ × V3)) (g : (s → ℝ × V3) → X0)
      (H : J.space ≃ₜ connectedComponentIn (frontier N) x),
      Continuous phi ∧
      (∀ i, LocallyPiecewiseAffineOn (phi ∘ (e i).symm) (e i).target) ∧
      J.faces.Finite ∧ PolyhedralPLInCharts e g J.space ∧
      (∀ z : J.space, (H z : X0) = g z) ∧
      (∀ z ∈ J.space, phi (g z) = z) ∧
      Nonempty (PeriodicSquare.SourceSquareMap 64 J) := by
  obtain ⟨s, phi, J, g, H, hphi, hphiPL, hJ, hconn, hzero, hpure, hcofaces, hlinks,
    hgPL, hH, hinverse, number, sigma, hcancel⟩ :=
    he.exists_original_oriented_component_euler_zero e hcover hcompat hN x hx hnt hinj
  exact ⟨s, phi, J, g, H, hphi, hphiPL, hJ, hgPL, hH, hinverse,
    OriginalTriangleCopies.nonempty_sourceSquareMap64_of_euler_zero_and_signs
      J hJ hconn hpure hcofaces hlinks hzero number sigma hcancel⟩

local notation "p" => (4 * (16 : ℝ))
local notation "C0" => AddCircle p
local notation "T0" => C0 × C0

open Classical in


theorem PLDomain.exists_original_frontier_torus_parametrization
    {ι : Type*} (e : ι → OpenPartialHomeomorph X0 V3)
    (hcover : ∀ x, ∃ i, x ∈ (e i).source)
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    {N : Set X0} (he : PLDomain e N) (hN : IsCompact N)
    (x : X0) (hx : x ∈ frontier N)
    (hnt : Nontrivial (FundamentalGroup (connectedComponentIn (frontier N) x)
      ⟨x, mem_connectedComponentIn hx⟩))
    (hinj : Function.Injective (FundamentalGroup.map
      (⟨Subtype.val, continuous_subtype_val⟩ :
        C(connectedComponentIn (frontier N) x, X0)) ⟨x, mem_connectedComponentIn hx⟩)) :
    ∃ d : ((Fin 0 → ℝ) × V3) → OpenPartialHomeomorph X0 V3,
      StandardLatticeHandleAtlas (Fin 0) (Fin 3) hamiltonZeroPeriodLattice d ∧
    ∃ (s : Finset N) (phi : X0 → (s → ℝ × V3))
      (J : SimplicialComplex ℝ (s → ℝ × V3)) (g : (s → ℝ × V3) → X0)
      (H : J.space ≃ₜ connectedComponentIn (frontier N) x)
      (T : T0 ≃ₜ connectedComponentIn (frontier N) x)
      (u : ℝ × ℝ → (s → ℝ × V3)),
      Continuous phi ∧
      (∀ i, LocallyPiecewiseAffineOn (phi ∘ (e i).symm) (e i).target) ∧
      J.faces.Finite ∧ PolyhedralPLInCharts e g J.space ∧
      (∀ z : J.space, (H z : X0) = g z) ∧
      (∀ y : connectedComponentIn (frontier N) x, (H.symm y : (s → ℝ × V3)) = phi y) ∧
      FinitePiecewiseAffineOn u (PeriodicSquare.squareCarrier p) ∧
      u '' PeriodicSquare.squareCarrier p = J.space ∧
      PolyhedralPLInCharts e (g ∘ u) (PeriodicSquare.squareCarrier p) ∧
      (g ∘ u) '' PeriodicSquare.squareCarrier p = connectedComponentIn (frontier N) x ∧
      (∀ z : PeriodicSquare.Square p,
        (T (PeriodicSquare.projection p z) : X0) = g (u (z.1, z.2))) ∧
      (∀ z w : PeriodicSquare.Square p,
        g (u (z.1, z.2)) = g (u (w.1, w.2)) ↔
          PeriodicSquare.projection p z = PeriodicSquare.projection p w) ∧
      ∀ theta : C0, PolyhedralPLInCharts d
        (hamiltonZeroCollarPhaseTarget J
          ⟨H.trans T.symm, (H.trans T.symm).continuous⟩ theta) J.space := by
  obtain ⟨d, hd⟩ := exists_zero_standard_lattice_handle_atlas
    (Fin 0) (Fin 3) hamiltonZeroPeriodLattice (by simp)
  refine ⟨d, hd, ?_⟩
  obtain ⟨s, phi, J, g, H, hphi, hphiPL, hJ, hgPL, hH, hinverse, ⟨M64⟩⟩ :=
    he.exists_original_frontier_torus_square_model e hcover hcompat hN x hx hnt hinj
  let M : PeriodicSquare.SourceSquareMap p J := by convert M64 using 1; norm_num
  obtain ⟨h, hvalue, hInvPL⟩ :=
    exists_PL_torus_parametrization_of_source_square_map hd hJ M
  obtain ⟨u, hu, huv⟩ := M.finite_piecewise_affine
  let T : T0 ≃ₜ connectedComponentIn (frontier N) x := h.trans H
  have huimage : u '' PeriodicSquare.squareCarrier p = J.space := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      let q : PeriodicSquare.Square p := (⟨z.1, hz.1⟩, ⟨z.2, hz.2⟩)
      rw [show u z = (M.map q : (s → ℝ × V3)) by simpa [q] using huv q]
      exact (M.map q).property
    · intro hy
      obtain ⟨z, hz⟩ := M.surjective ⟨y, hy⟩
      refine ⟨(z.1, z.2), ⟨z.1.property, z.2.property⟩, ?_⟩
      exact (huv z).trans (congrArg Subtype.val hz)
  have hgimage : g '' J.space = connectedComponentIn (frontier N) x := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact hH ⟨z, hz⟩ ▸ (H ⟨z, hz⟩).property
    · intro hy
      refine ⟨H.symm ⟨y, hy⟩, (H.symm ⟨y, hy⟩).property, ?_⟩
      rw [← hH, H.apply_symm_apply]
  have hforward : PolyhedralPLInCharts e (g ∘ u) (PeriodicSquare.squareCarrier p) := by
    obtain ⟨L, hL, hLs, hLu⟩ := hu
    rw [← hLs]
    exact hgPL.comp_finitePiecewiseAffineOn L hL (hLu.finitePiecewiseAffineOn hL)
      (fun z hz => huimage.subset ⟨z, hLs.subset hz, rfl⟩)
  have hTvalue (z : PeriodicSquare.Square p) :
      (T (PeriodicSquare.projection p z) : X0) = g (u (z.1, z.2)) := by
    change (H (h (PeriodicSquare.projection p z)) : X0) = _
    rw [hH, hvalue z, ← huv z]
  refine ⟨s, phi, J, g, H, T, u, hphi, hphiPL, hJ, hgPL, hH, ?_, hu, huimage,
    hforward, ?_, hTvalue, ?_, ?_⟩
  · intro y
    calc
      (H.symm y : (s → ℝ × V3)) = phi (g (H.symm y)) :=
        (hinverse _ (H.symm y).property).symm
      _ = phi y := by rw [← hH, H.apply_symm_apply]
  · rw [Set.image_comp, huimage, hgimage]
  · intro z w
    rw [← hTvalue z, ← hTvalue w]
    exact Subtype.val_injective.eq_iff.trans T.injective.eq_iff
  · intro theta
    have hcm : (⟨H.trans T.symm, (H.trans T.symm).continuous⟩ : C(J.space, T0)) =
        ⟨h.symm, h.symm.continuous⟩ := by
      apply ContinuousMap.ext
      intro z
      change h.symm (H.symm (H z)) = h.symm z
      rw [H.symm_apply_apply]
    rw [hcm]
    exact hInvPL theta

end PoincareConjecture.M76
