module

public import Mathlib.Topology.Homotopy.Lifting
public import PoincareConjecture.Proofs.Horizon.Topology.Covering.Universal.Basic
public import PoincareConjecture.Proofs.Horizon.Topology.Covering.Universal.LocalPathConnected

public section
noncomputable section

open scoped unitInterval
open Topology

variable {X : Type*} [TopologicalSpace X]

namespace Poincare.Topology.UniversalCover

variable {x₀ x : X}

theorem isCoveringMap [LocallyPathConnectedSpace X] [PathConnectedSpace X]
    [SemilocallySimplyConnectedSpace X] (x₀ : X) :
    IsCoveringMap (proj (x₀ := x₀)) := by
  intro x
  obtain ⟨U, hU_open, hxU, hU_pathConn, hU_slsc⟩ :=
    exists_isOpen_mem_isPathConnected_isPathHomotopyTrivial x
  let S := sheet (x₀ := x₀) U hxU
  have _ne_ι : Nonempty (Path.Homotopic.Quotient x₀ x) :=
    ⟨Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath x₀ x)⟩
  have _ne_fun : Nonempty (X → Poincare.Topology.UniversalCover x₀) :=
    ⟨fun _ ↦ ofBasedPath x₀ (BasedPath.ofPath (PathConnectedSpace.somePath x₀ x₀))⟩
  have h_open_iff : ∀ q : Path.Homotopic.Quotient x₀ x, ∀ {W : Set X}, W ⊆ U →
      (IsOpen W ↔ IsOpen (proj (x₀ := x₀) ⁻¹' W ∩ S q)) := by
    intro q W hWU
    refine ⟨fun hW ↦ (hW.preimage (continuous_proj x₀)).inter (isOpen_sheet U hU_open hxU q),
      fun h_open_inter ↦ ?_⟩
    have h := isOpenMap_proj x₀ _ h_open_inter
    rwa [Set.image_preimage_inter,
      Set.inter_eq_left.mpr (hWU.trans (proj_surjOn_sheet hU_pathConn hxU q))] at h
  refine ((IsEvenlyCovered.of_trivialization (t :=
    IsOpen.trivializationDiscrete (f := proj (x₀ := x₀))
      S U hU_open h_open_iff (proj_injOn_sheet hU_slsc hxU)
      (proj_surjOn_sheet hU_pathConn hxU) (pairwise_disjoint_sheet hU_slsc hxU)
      (sheet_exhaustive hU_pathConn hxU))
    ?_).to_isEvenlyCovered_preimage)
  rw [IsOpen.trivializationDiscrete_baseSet]
  exact hxU

instance discreteTopology_fiber [LocallyPathConnectedSpace X] [PathConnectedSpace X]
    [SemilocallySimplyConnectedSpace X] (x₀ x : X) :
    DiscreteTopology (proj (x₀ := x₀) ⁻¹' {x}) :=
  (isCoveringMap x₀ x).discreteTopology_fiber

theorem joined_basepoint_ofBasedPath (α : BasedPath x₀) :
    Joined (ofBasedPath x₀ (BasedPath.ofPath (Path.refl x₀))) (ofBasedPath x₀ α) :=
  ⟨{  toFun t := ofBasedPath x₀ (BasedPath.ofPath (Path.initialSegmentFamily α.toPath t))
      continuous_toFun :=
        (continuous_ofBasedPath x₀).comp <| by
          apply Continuous.subtype_mk
          exact ContinuousMap.continuous_of_continuous_uncurry _
            (Path.continuous_initialSegmentFamily_uncurry α.toPath)
      source' := by
        rw [Path.initialSegmentFamily_zero, ofBasedPath_ofPath]
        simp only [ofBasedPath_def]
        apply UniversalCover.ext α.2
        apply Path.Homotopic.hpath_hext
        intro t

        rfl
      target' := by
        rw [Path.initialSegmentFamily_one, ofBasedPath_def]
        simp only [ofBasedPath_def]
        apply UniversalCover.ext rfl
        apply Path.Homotopic.hpath_hext
        intro t

        rfl }⟩

instance pathConnectedSpace (x₀ : X) :
    PathConnectedSpace (Poincare.Topology.UniversalCover x₀) := by
  refine ⟨⟨ofBasedPath x₀ (BasedPath.ofPath (Path.refl x₀))⟩, fun z₁ z₂ ↦ ?_⟩
  obtain ⟨α₁, rfl⟩ := surjective_ofBasedPath x₀ z₁
  obtain ⟨α₂, rfl⟩ := surjective_ofBasedPath x₀ z₂
  exact (joined_basepoint_ofBasedPath α₁).symm.trans (joined_basepoint_ofBasedPath α₂)

private theorem ofBasedPath_append_initialSegmentFamily_zero {α : BasedPath x₀} {y : X}
    (γ : Path (BasedPath.endpoint α) y) :
    ofBasedPath x₀ (BasedPath.append α (Path.initialSegmentFamily γ 0)) = ofBasedPath x₀ α := by
  have h0_hom :
      Path.Homotopic
        ((α.toPath.trans (Path.initialSegmentFamily γ 0)).cast rfl
          (by simp))
        α.toPath := by
    rw [Path.initialSegmentFamily_zero]
    simpa using! Path.Homotopic.trans_refl α.toPath
  have h0_end : BasedPath.endpoint (BasedPath.append α (Path.initialSegmentFamily γ 0)) =
      BasedPath.endpoint α := by
    rw [BasedPath.endpoint_append]
    simp
  exact ofBasedPath_eq_of_homotopic_toPath (x₀ := x₀) h0_end h0_hom

private theorem ofBasedPath_append_initialSegmentFamily_one {α : BasedPath x₀} {y : X}
    (γ : Path (BasedPath.endpoint α) y) :
    ofBasedPath x₀ (BasedPath.append α (Path.initialSegmentFamily γ 1)) =
      ofBasedPath x₀ (BasedPath.append α γ) := by
  rw [Path.initialSegmentFamily_one]
  apply congrArg (ofBasedPath x₀)
  apply BasedPath.ext
  intro t

  change (α.toPath.trans (γ.cast _ _)) t = (α.toPath.trans γ) t
  rw [Path.trans_apply, Path.trans_apply]
  split_ifs <;> simp only [Path.cast_coe]

theorem liftPath_apply_one_eq_ofBasedPath_append
    [LocallyPathConnectedSpace X] [PathConnectedSpace X]
    [SemilocallySimplyConnectedSpace X] {α : BasedPath x₀} {y : X}
    (γ : Path (BasedPath.endpoint α) y) : (isCoveringMap x₀).liftPath γ (ofBasedPath x₀ α)
      (by simp) 1 =
      ofBasedPath x₀ (BasedPath.append α γ) := by
  let Γ : C(I, Poincare.Topology.UniversalCover x₀) := by
    refine ⟨fun t ↦ ofBasedPath x₀ (BasedPath.append α (Path.initialSegmentFamily γ t)),
      ?_⟩
    exact (continuous_ofBasedPath x₀).comp
      (BasedPath.continuous_append_initialSegmentFamily α γ)
  have hΓ_lifts : proj (x₀ := x₀) ∘ Γ = γ := by
    ext t

    rw [Function.comp_apply, show Γ t =
      ofBasedPath x₀ (BasedPath.append α (Path.initialSegmentFamily γ t)) from rfl,
      proj_ofBasedPath, BasedPath.endpoint_append]
  have hΓ_zero : Γ 0 = ofBasedPath x₀ α :=
    ofBasedPath_append_initialSegmentFamily_zero γ
  have hΓ_eq_lift :
      Γ = (isCoveringMap x₀).liftPath γ (ofBasedPath x₀ α)
        (by simp) :=
    ((isCoveringMap x₀).eq_liftPath_iff' (γ := γ)
      (e := ofBasedPath x₀ α)
      (γ_0 := by simp) (Γ := Γ)).2
      ⟨hΓ_lifts, hΓ_zero⟩
  rw [← hΓ_eq_lift]

  change ofBasedPath x₀ (BasedPath.append α (Path.initialSegmentFamily γ 1)) =
    ofBasedPath x₀ (BasedPath.append α γ)
  exact ofBasedPath_append_initialSegmentFamily_one γ

private theorem quotient_mk_eq_refl_of_ofBasedPath_append_eq {α : BasedPath x₀}
    (γ : Path (BasedPath.endpoint α) (BasedPath.endpoint α))
    (h_end : ofBasedPath x₀ (BasedPath.append α γ) = ofBasedPath x₀ α) :
    (Path.Homotopic.Quotient.mk γ : Path.Homotopic.Quotient
        (BasedPath.endpoint α) (BasedPath.endpoint α)) =
      Path.Homotopic.Quotient.refl (BasedPath.endpoint α) := by
  apply Quotient.sound
  apply Path.Homotopic.trans_left_cancel (e := α.toPath)
  have h := toPath_homotopic_of_ofBasedPath_eq h_end
  simp only [BasedPath.toPath_append] at h
  have h' : Path.Homotopic (α.toPath.trans γ) α.toPath := by
    convert h using 2
    ext t
    rfl
  exact h'.trans (Path.Homotopic.trans_refl α.toPath).symm

instance simplyConnectedSpace [LocallyPathConnectedSpace X] [PathConnectedSpace X]
    [SemilocallySimplyConnectedSpace X] (x₀ : X) :
    SimplyConnectedSpace (Poincare.Topology.UniversalCover x₀) := by
  rw [simply_connected_iff_loops_nullhomotopic]
  refine ⟨pathConnectedSpace x₀, ?_⟩
  intro z p
  obtain ⟨α, rfl⟩ := surjective_ofBasedPath x₀ z
  let γ : Path (BasedPath.endpoint α) (BasedPath.endpoint α) :=
    (p.map (continuous_proj x₀)).cast
      (proj_ofBasedPath x₀ α).symm (proj_ofBasedPath x₀ α).symm
  have hγ0 : γ 0 = proj (ofBasedPath x₀ α) := by
    rw [proj_ofBasedPath]
    exact γ.source
  have hp_eq_lift :
      (p : C(I, Poincare.Topology.UniversalCover x₀)) =
        (isCoveringMap x₀).liftPath γ (ofBasedPath x₀ α) hγ0 :=
    ((isCoveringMap x₀).eq_liftPath_iff' (γ := γ)
      (e := ofBasedPath x₀ α) (γ_0 := hγ0) (Γ := p)).2
      ⟨by ext t; rfl, p.source⟩
  have h_end : ofBasedPath x₀ (BasedPath.append α γ) = ofBasedPath x₀ α := by
    rw [← liftPath_apply_one_eq_ofBasedPath_append, ← hp_eq_lift]
    exact p.target
  have hγ_null := quotient_mk_eq_refl_of_ofBasedPath_append_eq γ h_end
  rw [← Path.Homotopic.Quotient.eq]
  apply (isCoveringMap x₀).injective_path_homotopic_map
    (ofBasedPath x₀ α) (ofBasedPath x₀ α)
  have hcast :=
    congrArg (Path.Homotopic.Quotient.cast · (proj_ofBasedPath x₀ α) (proj_ofBasedPath x₀ α))
      hγ_null
  simpa [γ, ← Path.Homotopic.Quotient.mk_map] using! hcast

theorem existsUnique_continuousMap_lifts {A : Type*} [TopologicalSpace A]
    [SimplyConnectedSpace A] [LocallyPathConnectedSpace A]
    [LocallyPathConnectedSpace X] [PathConnectedSpace X]
    [SemilocallySimplyConnectedSpace X] (x₀ : X)
    (f : C(A, X)) (a₀ : A) (e₀ : Poincare.Topology.UniversalCover x₀) (he : proj e₀ = f a₀) :
    ∃! F : C(A, Poincare.Topology.UniversalCover x₀), F a₀ = e₀ ∧ proj ∘ F = f :=
  (isCoveringMap x₀).existsUnique_continuousMap_lifts f a₀ e₀ he

theorem surjective_proj [PathConnectedSpace X] (x₀ : X) :
    Function.Surjective (proj (x₀ := x₀)) := by
  intro x
  exact ⟨⟨x, Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath x₀ x)⟩, rfl⟩

instance locallyPathConnectedSpace [LocallyPathConnectedSpace X] [PathConnectedSpace X]
    [SemilocallySimplyConnectedSpace X] (x₀ : X) :
    LocallyPathConnectedSpace (Poincare.Topology.UniversalCover x₀) :=
  (isCoveringMap x₀).isLocalHomeomorph.locallyPathConnectedSpace

end Poincare.Topology.UniversalCover

universe u

namespace Poincare.Topology

theorem exists_simplyConnected_cover (X : Type u) [TopologicalSpace X]
    [PathConnectedSpace X] [LocallyPathConnectedSpace X]
    [SemilocallySimplyConnectedSpace X] :
    ∃ (E : Type u) (t : TopologicalSpace E),
      letI : TopologicalSpace E := t
      SimplyConnectedSpace E ∧ LocallyPathConnectedSpace E ∧
        ∃ p : E → X, IsCoveringMap p ∧ Function.Surjective p := by
  classical
  let x₀ : X := Classical.arbitrary X
  exact ⟨UniversalCover x₀, inferInstance, inferInstance, inferInstance,
    UniversalCover.proj, UniversalCover.isCoveringMap x₀, UniversalCover.surjective_proj x₀⟩

end Poincare.Topology
