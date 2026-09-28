import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Capping.LiftedSphereCone
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Collars.SphereBicollarLevelCharts









set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

variable {X E ι : Type*} [TopologicalSpace X]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {e : ι → OpenPartialHomeomorph X V3} {S : Set X}

omit [FiniteDimensional ℝ E] in
theorem ChartwisePLSphere.exists_finitePL_model_parametrization
    (s : ChartwisePLSphere e S) (F : X → E)
    (hF : ∀ i, LocallyPiecewiseAffineOn (F ∘ (e i).symm) (e i).target)
    (hFi : InjOn F S) {N : Set E} (hN : N = F '' S) :
    ∃ H : sphere (0 : V3) 1 ≃ₜ N, H.IsFinitePL ∧
      ∀ x : sphere (0 : V3) 1, (H x : E) = F (s.map x) := by
  classical
  have hsimage : s.map '' sphere (0 : V3) 1 = S := by
    apply Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      rw [s.map_eq ⟨x, hx⟩]
      exact (s.parametrization ⟨x, hx⟩).property
    · intro y hy
      obtain ⟨x, hx⟩ := s.parametrization.surjective ⟨y, hy⟩
      exact ⟨x, x.property, (s.map_eq x).trans (congrArg Subtype.val hx)⟩
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKs, _⟩, _⟩, _⟩ :=
    (isFinitePLBallPair_unit_cube : IsFinitePLBallPair V3
      (closedBall (0 : V3) 1) (sphere (0 : V3) 1))
  let A := K.frontierSubcomplex (closedBall (0 : V3) 1)
  have hA : A.faces.Finite := K.frontierSubcomplex_finite _ hK
  have hAs : A.space = sphere (0 : V3) 1 := by
    rw [K.frontierSubcomplex_space isClosed_closedBall (convex_closedBall _ _)
      ⟨0, ball_subset_interior_closedBall (mem_ball_self zero_lt_one)⟩ hKs,
      frontier_closedBall _ one_ne_zero]
  have hsA : PolyhedralPLInCharts e s.map A.space := hAs.symm ▸ s.piecewiseAffine
  have hFs : FinitePiecewiseAffineOn (F ∘ s.map) (sphere (0 : V3) 1) := by
    rw [← hAs]
    exact hsA.finitePiecewiseAffineOn_comp A hA hF
  have hinj : InjOn (F ∘ s.map) (sphere (0 : V3) 1) := by
    intro x hx y hy hxy
    have hmap := hFi (hsimage.subset (mem_image_of_mem s.map hx))
      (hsimage.subset (mem_image_of_mem s.map hy)) hxy
    have hp : s.parametrization ⟨x, hx⟩ = s.parametrization ⟨y, hy⟩ :=
      Subtype.ext (by rw [← s.map_eq ⟨x, hx⟩, ← s.map_eq ⟨y, hy⟩]; exact hmap)
    exact congrArg Subtype.val (s.parametrization.injective hp)
  obtain ⟨H, hH, hval⟩ := hFs.exists_homeomorph_image hinj
  have himage : (F ∘ s.map) '' sphere (0 : V3) 1 = N := by
    calc
      _ = F '' (s.map '' sphere (0 : V3) 1) := (image_image F s.map _).symm
      _ = N := by rw [hsimage, ← hN]
  exact ⟨H.trans (Homeomorph.setCongr himage), hH.setCongr rfl himage, hval⟩

theorem ChartwisePLSphere.isFinitePLBallPair_model_cap
    (s : ChartwisePLSphere e S) (F : X → E)
    (hF : ∀ i, LocallyPiecewiseAffineOn (F ∘ (e i).symm) (e i).target)
    (hFi : InjOn F S) {N : Set E} (hN : N = F '' S) :
    IsFinitePLBallPair V3
      (convexJoin ℝ {((0 : E), (1 : ℝ))} ((fun x : E => (x, (0 : ℝ))) '' N))
      ((fun x : E => (x, (0 : ℝ))) '' N) := by
  obtain ⟨H, hH, _⟩ := s.exists_finitePL_model_parametrization F hF hFi hN
  have hfront : sphere (0 : V3) 1 = frontier (closedBall (0 : V3) 1) :=
    (frontier_closedBall _ one_ne_zero).symm
  have hne : N.Nonempty := by
    obtain ⟨x, hx⟩ := NormedSpace.sphere_nonempty (E := V3) (x := 0) |>.mpr (show (0 : ℝ) ≤ 1 by norm_num)
    exact ⟨H ⟨x, hx⟩, (H ⟨x, hx⟩).property⟩
  exact (hH.symm.setCongr rfl hfront).isFinitePLBallPair_lifted_sphere_cone
    hne (isCompact_closedBall _ _) (convex_closedBall _ _)
    ⟨0, ball_subset_interior_closedBall (mem_ball_self zero_lt_one)⟩

end PoincareConjecture.M76
