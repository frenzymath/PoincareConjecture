import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.GeometryImports
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.SourceNames
import PoincareLib.Geometry.RicciFlow.Blowup.Controlled.Geometry
import PoincareLib.Geometry.RicciFlow.Surgery.Induction.EpochExtension.Spacetime.GeneralizedBoxes
import PoincareLib.Geometry.Spacetime.Rescaling.Atlas.Construction

/-!
# The spacetime topology under parabolic rescaling

The new clock is `s = Q * (t - a)`. Pulling back the original spacetime
topology along `(s,x) -> (a+s/Q,x)` retains the actual generalized flow
topology, as in Morgan--Tian Definition 3.40, p. 61, and section 10.3,
p. 247. This is not the disjoint-union topology on the new sigma carrier.
-/

set_option autoImplicit false

universe u

namespace PoincareMT.M28

open scoped Topology

/-- The topology on the reindexed slices is transported from the original
spacetime. See Morgan--Tian Definition 3.40, printed p. 61. -/
@[instance_reducible]
noncomputable def rescaledSpaceTopology (F : GeneralizedRicciFlowData.{u}) (Q a : ℝ) :
    TopologicalSpace (Σ s : ℝ, (F.slice (parabolicTimeInv Q a s)).carrier) :=
  F.space_topology.induced (fun p ↦ (⟨parabolicTimeInv Q a p.1, p.2⟩ : F.point))

/-- The actual inverse-clock map is a spacetime homeomorphism. See
Morgan--Tian Definition 3.40, printed p. 61. -/
noncomputable def rescaledSpaceHomeomorph (F : GeneralizedRicciFlowData.{u})
    (Q : ℝ) (hQ : 0 < Q) (a : ℝ) :
    letI := rescaledSpaceTopology F Q a
    (Σ s : ℝ, (F.slice (parabolicTimeInv Q a s)).carrier) ≃ₜ F.point := by
  letI := rescaledSpaceTopology F Q a
  let e : (Σ s : ℝ, (F.slice (parabolicTimeInv Q a s)).carrier) ≃ F.point :=
    Equiv.sigmaCongrLeft (β := fun t ↦ (F.slice t).carrier)
      (parabolicTimeOrderIso Q hQ a).symm.toEquiv
  exact e.toHomeomorphOfIsInducing ⟨rfl⟩

/-- The spacetime homeomorphism uses the literal inverse-clock formula.
See Morgan--Tian Definition 3.40, printed p. 61. -/
@[simp]
theorem rescaledSpaceHomeomorph_apply (F : GeneralizedRicciFlowData.{u})
    (Q : ℝ) (hQ : 0 < Q) (a : ℝ)
    (p : Σ s : ℝ, (F.slice (parabolicTimeInv Q a s)).carrier) :
    rescaledSpaceHomeomorph F Q hQ a p = ⟨parabolicTimeInv Q a p.1, p.2⟩ := rfl

/-- Hausdorffness is preserved by the actual spacetime reindexing.
See Morgan--Tian Definition 3.40, printed p. 61. -/
theorem rescaledSpace_t2 (F : GeneralizedRicciFlowData.{u})
    (Q : ℝ) (hQ : 0 < Q) (a : ℝ) :
    letI := rescaledSpaceTopology F Q a
    T2Space (Σ s : ℝ, (F.slice (parabolicTimeInv Q a s)).carrier) := by
  let := rescaledSpaceTopology F Q a
  let : T2Space F.point := F.space_t2
  exact (rescaledSpaceHomeomorph F Q hQ a).isEmbedding.t2Space

/-- Second countability is preserved by the actual spacetime reindexing.
See Morgan--Tian Definition 3.40, printed p. 61. -/
theorem rescaledSpace_secondCountable (F : GeneralizedRicciFlowData.{u})
    (Q : ℝ) (hQ : 0 < Q) (a : ℝ) :
    letI := rescaledSpaceTopology F Q a
    SecondCountableTopology (Σ s : ℝ, (F.slice (parabolicTimeInv Q a s)).carrier) := by
  let := rescaledSpaceTopology F Q a
  let : SecondCountableTopology F.point := F.space_secondCountable
  exact (rescaledSpaceHomeomorph F Q hQ a).isEmbedding.secondCountableTopology

/-- The new time projection is the affine transform of the old continuous
time projection. See Morgan--Tian Definition 3.40, printed p. 61. -/
theorem rescaledSpace_time_continuous (F : GeneralizedRicciFlowData.{u})
    (Q : ℝ) (hQ : 0 < Q) (a : ℝ) :
    letI := rescaledSpaceTopology F Q a
    Continuous (Sigma.fst : (Σ s : ℝ, (F.slice (parabolicTimeInv Q a s)).carrier) → ℝ) := by
  let := rescaledSpaceTopology F Q a
  have h : Continuous (fun p : Σ s : ℝ, (F.slice (parabolicTimeInv Q a s)).carrier ↦
      parabolicTime Q a (rescaledSpaceHomeomorph F Q hQ a p).1) :=
    continuous_const.mul
      ((F.time_continuous.comp (rescaledSpaceHomeomorph F Q hQ a).continuous).sub continuous_const)
  simpa only [rescaledSpaceHomeomorph_apply, parabolicTime_parabolicTimeInv Q hQ] using h

/-- Each reindexed slice keeps its original embedding into spacetime.
See Morgan--Tian Definition 3.40, printed p. 61. -/
theorem rescaledSpace_slice_embedding (F : GeneralizedRicciFlowData.{u})
    (Q : ℝ) (hQ : 0 < Q) (a s : ℝ) :
    letI := rescaledSpaceTopology F Q a
    Topology.IsEmbedding (fun x : (F.slice (parabolicTimeInv Q a s)).carrier ↦
      (⟨s, x⟩ : Σ v : ℝ, (F.slice (parabolicTimeInv Q a v)).carrier)) := by
  let := rescaledSpaceTopology F Q a
  apply (rescaledSpaceHomeomorph F Q hQ a).isEmbedding.of_comp_iff.mp
  exact F.slice_embedding (parabolicTimeInv Q a s)

/-- The rescaled box map is an open embedding by the original box map,
the interval clock homeomorphism and the spacetime homeomorphism. See
Morgan--Tian Definition 3.40, printed p. 61. -/
theorem rescaledSpace_box_openEmbedding (F : GeneralizedRicciFlowData.{u})
    (Q : ℝ) (hQ : 0 < Q) (a : ℝ) (b : F.box_index) :
    letI := rescaledSpaceTopology F Q a
    Topology.IsOpenEmbedding
      (fun p : (parabolicInterval Q hQ a (Proofs.M12.boxInterval F b)).domain ×
          (F.box b).carrier.carrier ↦
        (⟨p.1.1, (F.box b).forward (parabolicTimeInv Q a p.1.1)
          ((mem_parabolicInterval_iff Q hQ a (Proofs.M12.boxInterval F b) p.1.1).mp p.1.2)
          p.2⟩ : Σ s : ℝ, (F.slice (parabolicTimeInv Q a s)).carrier)) := by
  let := rescaledSpaceTopology F Q a
  let H := rescaledSpaceHomeomorph F Q hQ a
  let T := (M13.timeHomeomorph Q hQ a (Proofs.M12.boxInterval F b)).symm.prodCongr
    (Homeomorph.refl (F.box b).carrier.carrier)
  have h := H.symm.isOpenEmbedding.comp ((F.box_openEmbedding b).comp T.isOpenEmbedding)
  convert h using 1
  funext p
  apply H.injective
  simp only [Function.comp_apply, Homeomorph.apply_symm_apply]
  rfl

end PoincareMT.M28
