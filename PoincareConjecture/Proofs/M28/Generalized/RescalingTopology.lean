import PoincareConjecture.Definitions.Ch11.BlowupLimits
import PoincareConjecture.Proofs.M12.GeneralizedBoxes
import PoincareConjecture.Proofs.M13.Atlas

set_option autoImplicit false

universe u

namespace PoincareConjecture.M28

open scoped Topology

@[instance_reducible]
noncomputable def rescaledSpaceTopology (F : GeneralizedRicciFlowData.{u}) (Q a : ℝ) :
    TopologicalSpace (Σ s : ℝ, (F.slice (parabolicTimeInv Q a s)).carrier) :=
  F.space_topology.induced (fun p ↦ (⟨parabolicTimeInv Q a p.1, p.2⟩ : F.point))

noncomputable def rescaledSpaceHomeomorph (F : GeneralizedRicciFlowData.{u})
    (Q : ℝ) (hQ : 0 < Q) (a : ℝ) :
    letI := rescaledSpaceTopology F Q a
    (Σ s : ℝ, (F.slice (parabolicTimeInv Q a s)).carrier) ≃ₜ F.point := by
  letI := rescaledSpaceTopology F Q a
  let e : (Σ s : ℝ, (F.slice (parabolicTimeInv Q a s)).carrier) ≃ F.point :=
    Equiv.sigmaCongrLeft (β := fun t ↦ (F.slice t).carrier)
      (parabolicTimeOrderIso Q hQ a).symm.toEquiv
  exact e.toHomeomorphOfIsInducing ⟨rfl⟩

@[simp]
theorem rescaledSpaceHomeomorph_apply (F : GeneralizedRicciFlowData.{u})
    (Q : ℝ) (hQ : 0 < Q) (a : ℝ)
    (p : Σ s : ℝ, (F.slice (parabolicTimeInv Q a s)).carrier) :
    rescaledSpaceHomeomorph F Q hQ a p = ⟨parabolicTimeInv Q a p.1, p.2⟩ := rfl

theorem rescaledSpace_t2 (F : GeneralizedRicciFlowData.{u})
    (Q : ℝ) (hQ : 0 < Q) (a : ℝ) :
    letI := rescaledSpaceTopology F Q a
    T2Space (Σ s : ℝ, (F.slice (parabolicTimeInv Q a s)).carrier) := by
  let := rescaledSpaceTopology F Q a
  let : T2Space F.point := F.space_t2
  exact (rescaledSpaceHomeomorph F Q hQ a).isEmbedding.t2Space

theorem rescaledSpace_secondCountable (F : GeneralizedRicciFlowData.{u})
    (Q : ℝ) (hQ : 0 < Q) (a : ℝ) :
    letI := rescaledSpaceTopology F Q a
    SecondCountableTopology (Σ s : ℝ, (F.slice (parabolicTimeInv Q a s)).carrier) := by
  let := rescaledSpaceTopology F Q a
  let : SecondCountableTopology F.point := F.space_secondCountable
  exact (rescaledSpaceHomeomorph F Q hQ a).isEmbedding.secondCountableTopology

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

theorem rescaledSpace_slice_embedding (F : GeneralizedRicciFlowData.{u})
    (Q : ℝ) (hQ : 0 < Q) (a s : ℝ) :
    letI := rescaledSpaceTopology F Q a
    Topology.IsEmbedding (fun x : (F.slice (parabolicTimeInv Q a s)).carrier ↦
      (⟨s, x⟩ : Σ v : ℝ, (F.slice (parabolicTimeInv Q a v)).carrier)) := by
  let := rescaledSpaceTopology F Q a
  apply (rescaledSpaceHomeomorph F Q hQ a).isEmbedding.of_comp_iff.mp
  exact F.slice_embedding (parabolicTimeInv Q a s)

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

end PoincareConjecture.M28
