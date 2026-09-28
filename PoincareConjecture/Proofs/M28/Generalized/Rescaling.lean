import PoincareConjecture.Proofs.M28.Generalized.RescalingTopology
import PoincareConjecture.Proofs.M13.OrdinaryFlow










set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture.M28



noncomputable def rescaledFlowBox (F : GeneralizedRicciFlowData.{u})
    (Q : ℝ) (hQ : 0 < Q) (a : ℝ) (b : F.box_index) :
    GeneralizedRicciFlowBox
      (fun s ↦ F.slice (parabolicTimeInv Q a s))
      (fun s ↦ M13.scaleSmoothMetric (F.metric (parabolicTimeInv Q a s)) Q hQ)
      (parabolicInterval Q hQ a (Proofs.M12.flowInterval F)).domain := by
  let R := Classical.choice (M13.ordinaryParabolicRescaling (Proofs.M12.boxInterval F b)
    (F.box b).flow Q hQ a)
  let oldTimeMem (s : ℝ)
      (hs : s ∈ (parabolicInterval Q hQ a (Proofs.M12.boxInterval F b)).domain) :
      parabolicTimeInv Q a s ∈ (F.box b).interval :=
    (mem_parabolicInterval_iff Q hQ a (Proofs.M12.boxInterval F b) s).mp hs
  exact {
    carrier := (F.box b).carrier
    interval := (parabolicInterval Q hQ a (Proofs.M12.boxInterval F b)).domain
    relatively_open := M13.interval_relatively_open Q hQ a
      (Proofs.M12.flowInterval F) (Proofs.M12.boxInterval F b) (F.box b).relatively_open
    flow := R.flow
    forward := fun s hs ↦ (F.box b).forward (parabolicTimeInv Q a s) (oldTimeMem s hs)
    inverse := fun s hs ↦ (F.box b).inverse (parabolicTimeInv Q a s) (oldTimeMem s hs)
    forward_openEmbedding := fun s hs ↦
      (F.box b).forward_openEmbedding (parabolicTimeInv Q a s) (oldTimeMem s hs)
    forward_smooth := fun s hs ↦
      (F.box b).forward_smooth (parabolicTimeInv Q a s) (oldTimeMem s hs)
    inverse_smooth := fun s hs ↦
      (F.box b).inverse_smooth (parabolicTimeInv Q a s) (oldTimeMem s hs)
    left_inverse := fun s hs ↦
      (F.box b).left_inverse (parabolicTimeInv Q a s) (oldTimeMem s hs)
    right_inverse := fun s hs ↦
      (F.box b).right_inverse (parabolicTimeInv Q a s) (oldTimeMem s hs)
    metric_pullback := by
      intro s hs x v w
      rw [M13.scaleSmoothMetric_inner, R.metric_eq]
      exact congrArg (fun z : ℝ ↦ Q * z)
        ((F.box b).metric_pullback (parabolicTimeInv Q a s) (oldTimeMem s hs) x v w) }




noncomputable def rescale (F : GeneralizedRicciFlowData.{u})
    (Q : ℝ) (hQ : 0 < Q) (a : ℝ) : GeneralizedRicciFlowData.{u} where
  slice s := F.slice (parabolicTimeInv Q a s)
  interval := (parabolicInterval Q hQ a (Proofs.M12.flowInterval F)).domain
  interval_connected := (parabolicInterval Q hQ a (Proofs.M12.flowInterval F)).ordConnected
  interval_nontrivial := (parabolicInterval Q hQ a (Proofs.M12.flowInterval F)).nontrivial
  slice_nonempty_iff s := (F.slice_nonempty_iff (parabolicTimeInv Q a s)).trans
    (mem_parabolicInterval_iff Q hQ a (Proofs.M12.flowInterval F) s).symm
  metric s := M13.scaleSmoothMetric (F.metric (parabolicTimeInv Q a s)) Q hQ
  connection s := M13.scaleLeviCivitaData (F.connection (parabolicTimeInv Q a s)) Q hQ
  space_topology := rescaledSpaceTopology F Q a
  space_t2 := rescaledSpace_t2 F Q hQ a
  space_secondCountable := rescaledSpace_secondCountable F Q hQ a
  time_continuous := rescaledSpace_time_continuous F Q hQ a
  slice_embedding := rescaledSpace_slice_embedding F Q hQ a
  box_index := F.box_index
  box := rescaledFlowBox F Q hQ a
  box_openEmbedding := rescaledSpace_box_openEmbedding F Q hQ a
  box_covers := by
    intro s x
    obtain ⟨b, ht, y, hy⟩ := F.box_covers (parabolicTimeInv Q a s) x
    exact ⟨b, (mem_parabolicInterval_iff Q hQ a (Proofs.M12.boxInterval F b) s).mpr ht,
      y, hy⟩
  vertical_compatibility := by
    intro b c s hb hc x y hxy v hv hv'
    exact F.vertical_compatibility b c (parabolicTimeInv Q a s) _ _ x y hxy
      (parabolicTimeInv Q a v) _ _



@[simp]
theorem mem_rescale_interval (F : GeneralizedRicciFlowData.{u})
    (Q : ℝ) (hQ : 0 < Q) (a s : ℝ) :
    s ∈ (rescale F Q hQ a).interval ↔ parabolicTimeInv Q a s ∈ F.interval :=
  mem_parabolicInterval_iff Q hQ a (Proofs.M12.flowInterval F) s



theorem rescale_scalar (F : GeneralizedRicciFlowData.{u})
    (Q : ℝ) (hQ : 0 < Q) (a s : ℝ) (x : (rescale F Q hQ a).slice s |>.carrier) :
    (rescale F Q hQ a).scalar ⟨s, x⟩ =
      F.scalar ⟨parabolicTimeInv Q a s, x⟩ / Q := by
  exact M13.homothety_scalarCurvature_eq
    (F.metric (parabolicTimeInv Q a s)) ((rescale F Q hQ a).metric s)
    (Diffeomorph.refl (𝓡 3) (F.slice (parabolicTimeInv Q a s)).carrier ∞) Q hQ
    (M13.identity_metricHomothety _ Q hQ)
    (F.connection (parabolicTimeInv Q a s)) ((rescale F Q hQ a).connection s) x




theorem rescale_edist (F : GeneralizedRicciFlowData.{u})
    (Q : ℝ) (hQ : 0 < Q) (a s : ℝ)
    (x y : (rescale F Q hQ a).slice s |>.carrier) :
    ((rescale F Q hQ a).metric s).edist x y =
      ENNReal.ofReal (Real.sqrt Q) * (F.metric (parabolicTimeInv Q a s)).edist x y := by
  exact M13.homothety_edist
    (F.metric (parabolicTimeInv Q a s)) ((rescale F Q hQ a).metric s)
    (Diffeomorph.refl (𝓡 3) (F.slice (parabolicTimeInv Q a s)).carrier ∞) Q hQ
    (M13.identity_metricHomothety _ Q hQ) x y

end PoincareConjecture.M28
