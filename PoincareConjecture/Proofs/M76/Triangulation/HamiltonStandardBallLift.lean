import PoincareConjecture.Proofs.M76.Triangulation.HamiltonStandardFinitePLSphere
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonStandardDeckRegions
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonAlexanderConsequences
import PoincareConjecture.Proofs.M76.Mathlib.ConvexFrontierSphereTopology
import PoincareConjecture.Proofs.M76.Mathlib.ConvexPolyhedralNeighborhood










set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76

variable (ι κ : Type*) [Fintype ι] [Fintype κ]
  (L : Submodule ℤ (κ → ℝ)) [DiscreteTopology L]
  {α : Type*}
  {d : α → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) (Fin 3 → ℝ)}
  {S : Set (LatticeHandleAmbient ι κ L)}

local notation "V" => ((ι → ℝ) × (κ → ℝ))
local notation "W" => LatticeHandleAmbient ι κ L
local notation "pi" => (fun x : V =>
  (Prod.fst x, (QuotientAddGroup.mk (Prod.snd x) : (κ → ℝ) ⧸ L.toAddSubgroup)))






theorem ChartwisePLSphere.exists_standard_lattice_ball_lift
    (s : ChartwisePLSphere d S) (hd : StandardLatticeHandleAtlas ι κ L d)
    (hdim : Fintype.card ι + Fintype.card κ = 3)
    (hSR : S ⊆ latticeHandleDomain ι κ L) :
    ∃ B T : Set V,
      IsFinitePLBallPair ((ℝ × ℝ) × ℝ) B T ∧ InjOn pi B ∧
      pi '' T = S ∧ B ⊆ closedBall (0 : ι → ℝ) 1 ×ˢ (univ : Set (κ → ℝ)) := by
  classical
  obtain ⟨T, l, hl, hquot⟩ := s.exists_finitePL_standard_lattice_lift hd
  let qT : T ≃ₜ S := l.symm.trans s.parametrization
  have hpi (x : T) : pi x = (qT x : W) := by
    change pi x = (s.parametrization (l.symm x) : W)
    simpa only [l.apply_symm_apply] using hquot (l.symm x)
  have hTimage : pi '' T = S := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [hpi ⟨y, hy⟩]
      exact (qT ⟨y, hy⟩).property
    · intro hx
      refine ⟨qT.symm ⟨x, hx⟩, (qT.symm ⟨x, hx⟩).property, ?_⟩
      rw [hpi]
      exact congrArg Subtype.val (qT.apply_symm_apply ⟨x, hx⟩)
  have hpT : InjOn pi T := by
    intro x hx y hy hxy
    have heq : qT ⟨x, hx⟩ = qT ⟨y, hy⟩ :=
      Subtype.ext ((hpi ⟨x, hx⟩).symm.trans (hxy.trans (hpi ⟨y, hy⟩)))
    exact congrArg Subtype.val (qT.injective heq)
  let : CompactSpace (sphere (0 : Fin 3 → ℝ) 1) :=
    isCompact_iff_compactSpace.mp (isCompact_sphere _ _)
  let : CompactSpace T := l.compactSpace
  have hT : IsCompact T := isCompact_iff_compactSpace.mpr inferInstance
  let e := l.symm.trans (Homeomorph.setCongr
    (frontier_closedBall (0 : Fin 3 → ℝ) one_ne_zero).symm)
  have he : e.IsFinitePL := hl.symm.setCongr rfl
    (frontier_closedBall (0 : Fin 3 → ℝ) one_ne_zero).symm
  have hTc : IsConnected T := e.isConnected_of_convex_frontier
    (isCompact_closedBall _ _) (convex_closedBall _ _)
    ⟨0, ball_subset_interior_closedBall (mem_ball_self zero_lt_one)⟩ (by simp)
  obtain ⟨J, hJ, hJcv, hTJ⟩ := hT.exists_finite_convex_neighborhood
  have hJne : (interior J.space).Nonempty := hTc.nonempty.mono hTJ
  have hdimV : Module.finrank ℝ V = 3 := by simpa [Module.finrank_prod] using hdim
  obtain ⟨U, hU, hUc, hUf, _, hB, _⟩ := he.hasAlexanderRegionBalls
    (isCompact_closedBall _ _) (convex_closedBall _ _)
    ⟨0, ball_subset_interior_closedBall (mem_ball_self zero_lt_one)⟩
    (by simp) hdimV (J.isCompact_space_of_finite hJ) hJcv hJne hTJ J hJ rfl
  have hUb : Bornology.IsBounded U := hB.isCompact.isBounded.subset subset_closure
  let p : V →+ W := (AddMonoidHom.id (ι → ℝ)).prodMap
    (QuotientAddGroup.mk' L.toAddSubgroup)
  have hpinj : InjOn pi (closure U) :=
    injOn_closure_of_injOn_connected_frontier p hU hUb hUc
      (hUf.symm ▸ hTc) (hUf.symm ▸ hpT)
  refine ⟨closure U, T, hB, hpinj, hTimage, ?_⟩
  have hTbound (y : V) (hy : y ∈ frontier U) (i : ι) : |y.1 i| ≤ 1 := by
    have hyS : pi y ∈ S := hTimage ▸ mem_image_of_mem pi (hUf ▸ hy)
    have hyR := hSR hyS
    have hnorm : ‖y.1‖ ≤ 1 := mem_closedBall_zero_iff.mp hyR.1
    simpa only [Real.norm_eq_abs] using (norm_le_pi_norm y.1 i).trans hnorm
  intro x hx
  refine ⟨mem_closedBall_zero_iff.mpr ?_, mem_univ _⟩
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mpr
  intro i
  let A : V →ᵃ[ℝ] ℝ :=
    ((LinearMap.proj i).comp (LinearMap.fst ℝ (ι → ℝ) (κ → ℝ))).toAffineMap
  have hv : 0 < A.linear (Pi.single i 1, 0) := by simp [A]
  have hupper : x.1 i ≤ 1 := hU.affine_le_on_closure_of_le_frontier hUb A _ hv
    (fun y hy => (abs_le.mp (hTbound y hy i)).2) x hx
  have hnv : 0 < (-A).linear (-(Pi.single i 1, 0)) := by
    change 0 < -(A.linear (-((Pi.single i 1, 0) : V)))
    rw [map_neg, neg_neg]
    exact hv
  have hneg := hU.affine_le_on_closure_of_le_frontier hUb (-A) _ hnv
    (a := 1) (fun y hy => by
      change -y.1 i ≤ 1
      linarith [(abs_le.mp (hTbound y hy i)).1]) x hx
  change -x.1 i ≤ 1 at hneg
  rw [Real.norm_eq_abs]
  exact abs_le.mpr ⟨by linarith, hupper⟩

end PoincareConjecture.M76
