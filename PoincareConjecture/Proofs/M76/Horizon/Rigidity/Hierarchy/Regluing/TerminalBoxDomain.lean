import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Regluing.TerminalBoundaryMap
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.FiniteConvexDomain
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Coordinates.PLAtlasTransport
import PoincareConjecture.Proofs.M76.Rigidity.StandardHierarchyParameterPL









set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "E3" => ((ℝ × ℝ) × ℝ)

noncomputable def terminalBoxCoordinates : E3 ≃ᴬ[ℝ] V3 :=
  (ContinuousLinearEquiv.ofFinrankEq (by simp [Module.finrank_prod]) :
    E3 ≃L[ℝ] V3).toContinuousAffineEquiv

noncomputable def terminalBoxAtlas : Unit → OpenPartialHomeomorph E3 V3 :=
  fun _ => terminalBoxCoordinates.toHomeomorph.transOpenPartialHomeomorph
    (Homeomorph.refl V3).toOpenPartialHomeomorph

theorem plDomain_terminalBox {u v a b alpha beta : ℝ}
    (huv : u < v) (hab : a < b) (halpha : alpha < beta) :
    PLDomain terminalBoxAtlas ((Icc u v ×ˢ Icc a b) ×ˢ Icc alpha beta) := by
  classical
  let S : Set E3 := (Icc u v ×ˢ Icc a b) ×ˢ Icc alpha beta
  let c := terminalBoxCoordinates
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKS, _⟩, _⟩, _⟩ :=
    ((isFinitePLBallPair_Icc huv).prod (isFinitePLBallPair_Icc hab)).prod
      (isFinitePLBallPair_Icc halpha)
  have hcK : K.AffineOnFaces c := K.affineOnFaces_affine c.toContinuousAffineMap
  let J := hcK.embeddedImage c.injective.injOn
  have hJ : J.faces.Finite := hcK.embeddedImage_finite _ hK
  have hJS : J.space = c '' S := by rw [hcK.embeddedImage_space, hKS]
  have hcompact : IsCompact (c '' S) :=
    ((isCompact_Icc.prod isCompact_Icc).prod isCompact_Icc).image c.continuous
  have hcv : Convex ℝ (c '' S) :=
    (((convex_Icc u v).prod (convex_Icc a b)).prod (convex_Icc alpha beta)).affine_image
      c.toAffineEquiv.toAffineMap
  have hmid : (((u + v) / 2, (a + b) / 2), (alpha + beta) / 2) ∈ interior S := by
    simp only [S, interior_prod_eq, interior_Icc, mem_prod, mem_Ioo]
    exact ⟨⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩,
      ⟨by linarith, by linarith⟩⟩
  have hne : (interior (c '' S)).Nonempty := by
    change (interior (c.toHomeomorph '' S)).Nonempty
    rw [← c.toHomeomorph.image_interior]
    exact ⟨_, mem_image_of_mem c hmid⟩
  have hp : ((u, a), alpha) ∈ frontier S := by
    exact (mem_frontier_three_interval_box_iff
      (show ((u, a), alpha) ∈ S from
        ⟨⟨⟨le_rfl, huv.le⟩, ⟨le_rfl, hab.le⟩⟩, ⟨le_rfl, halpha.le⟩⟩)).mpr
      (Or.inl (Or.inl rfl))
  have hq : ((v, a), alpha) ∈ frontier S := by
    exact (mem_frontier_three_interval_box_iff
      (show ((v, a), alpha) ∈ S from
        ⟨⟨⟨huv.le, le_rfl⟩, ⟨le_rfl, hab.le⟩⟩, ⟨le_rfl, halpha.le⟩⟩)).mpr
      (Or.inl (Or.inr rfl))
  have hfront {x : E3} (hx : x ∈ frontier S) : c x ∈ frontier (c '' S) := by
    change c.toHomeomorph x ∈ frontier (c.toHomeomorph '' S)
    rw [← c.toHomeomorph.image_frontier]
    exact mem_image_of_mem c hx
  have hdomain := J.plDomain_convex_of_frontier_points hJ hcompact hcv hne hJS
    (hfront hp) (hfront hq) (by
      intro h
      exact huv.ne (congrArg (fun z : E3 => z.1.1) (c.injective h)))
  have hpull := hdomain.preimage_homeomorph c.toHomeomorph
  have heq : c.toHomeomorph ⁻¹' (c '' S) = S := c.injective.preimage_image S
  rw [heq] at hpull
  exact hpull

theorem polyhedralPL_terminalBoxAtlas_of_finitePiecewiseAffineOn
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {S : Set E} {f : E → E3} (hf : FinitePiecewiseAffineOn f S) :
    PolyhedralPLInCharts terminalBoxAtlas f S := by
  obtain ⟨K, hK, hKS, hc⟩ := hf.postcomp terminalBoxCoordinates.toContinuousAffineMap
  refine ⟨hf.continuousOn, ?_⟩
  intro x
  refine ⟨(), K, univ, hK, hKS.subset, isOpen_univ, trivial, ?_, ?_, ?_⟩
  · rintro _ ⟨z, _, rfl⟩
    exact hKS.symm.subset z.property
  · intro z hz
    trivial
  · exact ⟨K, hK, rfl, hc⟩

end PoincareConjecture.M76
