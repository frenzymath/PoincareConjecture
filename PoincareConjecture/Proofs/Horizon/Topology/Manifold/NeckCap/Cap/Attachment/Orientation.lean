import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Attachment.ClosingTails
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Tube.Gluing.Finite.Certificate











set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture

private def openUnitIntervalReflection : Ioo (0 : ℝ) 1 ≃ₜ Ioo (0 : ℝ) 1 where
  toFun t := ⟨1 - t, by constructor <;> linarith [t.property.1, t.property.2]⟩
  invFun t := ⟨1 - t, by constructor <;> linarith [t.property.1, t.property.2]⟩
  left_inv t := by ext; dsimp; ring
  right_inv t := by ext; dsimp; ring
  continuous_toFun := by
    fun_prop
  continuous_invFun := by
    fun_prop

namespace OpenCylinderModel

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  {U : Set M}


def reversed (T : OpenCylinderModel U) : OpenCylinderModel U where
  homeomorph := ((Homeomorph.refl UnitTwoSphere).prodCongr
    openUnitIntervalReflection).trans T.homeomorph
  coordinate z := T.coordinate (z.1, 1 - z.2)
  coordinate_eq z := by
    simpa [openUnitIntervalReflection, Prod.map_def] using
      T.coordinate_eq (z.1, openUnitIntervalReflection z.2)
  coordinate_smooth := T.coordinate_smooth.comp
    (contMDiff_fst.prodMk (contMDiff_const.sub contMDiff_snd)).contMDiffOn
    (by intro z hz; exact ⟨mem_univ _, by constructor <;> linarith [hz.2.1, hz.2.2]⟩)
  inverse x := ((T.inverse x).1, 1 - (T.inverse x).2)
  inverse_mem x hx := ⟨mem_univ _, by
    have h := (T.inverse_mem x hx).2
    constructor <;> linarith [h.1, h.2]⟩
  left_inverse := by
    intro z hz
    have hr : (z.1, 1 - z.2) ∈ univ ×ˢ Ioo (0 : ℝ) 1 :=
      ⟨mem_univ _, by constructor <;> linarith [hz.2.1, hz.2.2]⟩
    dsimp only
    rw [T.left_inverse hr]
    simp only [sub_sub_cancel, Prod.eta]
  right_inverse := by
    intro x hx
    dsimp
    rw [sub_sub_cancel, Prod.eta, T.right_inverse hx]
  inverse_smooth := (contMDiff_fst.prodMk (contMDiff_const.sub contMDiff_snd)).comp_contMDiffOn
    T.inverse_smooth


theorem reversed_tail (T : OpenCylinderModel U) (side : Bool) (a : ℝ) :
    T.reversed.tail side a = T.tail (!side) (1 - a) := by
  cases side <;> ext x <;> constructor
  all_goals
    rintro ⟨⟨q, t⟩, ⟨_, ht⟩, hxt⟩
    refine ⟨(q, 1 - t), ⟨mem_univ _, ?_⟩, ?_⟩
  all_goals first
    | (change 1 - a < 1 - t ∧ 1 - t < 1; constructor <;> linarith [ht.1, ht.2])
    | (change 0 < 1 - t ∧ 1 - t < a; constructor <;> linarith [ht.1, ht.2])
    | (change 0 < 1 - t ∧ 1 - t < 1 - a; constructor <;> linarith [ht.1, ht.2])
    | (change a < 1 - t ∧ 1 - t < 1; constructor <;> linarith [ht.1, ht.2])
    | exact hxt
    | (change T.coordinate (q, 1 - (1 - t)) = x; simpa only [sub_sub_cancel] using hxt)


theorem reversed_middleSphere (T : OpenCylinderModel U) :
    T.reversed.middleSphere = T.middleSphere := by
  ext x
  constructor <;> rintro ⟨⟨q, t⟩, ⟨_, ht⟩, hxt⟩
  all_goals
    have ht' : t = (1 / 2 : ℝ) := ht
    subst t
    refine ⟨(q, 1 / 2), ⟨mem_univ _, rfl⟩, ?_⟩
    simpa only [reversed, show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num] using hxt

end OpenCylinderModel

namespace EpsilonTubeCertificate

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  {g : RiemannianMetric 3 M} {X : Set M}


def reversedCylinder (tube : EpsilonTubeCertificate g X) : EpsilonTubeCertificate g X :=
  { tube with
    cylinder := tube.cylinder.reversed
    central_sphere_isotopy := by
      intro i hi
      rw [tube.cylinder.reversed_middleSphere]
      exact tube.central_sphere_isotopy i hi }

end EpsilonTubeCertificate

namespace CapTubeAttachment

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  {g : RiemannianMetric 3 M} {X : Set M}
  {C : CapCertificate g} {tube : EpsilonTubeCertificate g X} {side : Bool}


def reversedCylinder (A : CapTubeAttachment C tube side) :
    CapTubeAttachment C tube.reversedCylinder (!side) where
  overlap_model := A.overlap_model
  tube_tail := by
    obtain ⟨a, ha, htail⟩ := A.tube_tail
    refine ⟨1 - a, ⟨by linarith [ha.2], by linarith [ha.1]⟩, ?_⟩
    change tube.cylinder.reversed.tail (!side) (1 - a) ⊆ C.carrier
    rw [tube.cylinder.reversed_tail, Bool.not_not, sub_sub_cancel]
    exact htail
  cap_tail := A.cap_tail

end CapTubeAttachment

namespace CapCertificate




theorem exists_finite_chain_oriented_attachment_tails_threshold :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 10000 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M},
        ∀ (C D : CapCertificate g), C.epsilon ≤ ε₀ → D.epsilon = C.epsilon →
        ∀ (H : ConnectedNeckCapCover g) (T : BalancedNeckChain g C.epsilon),
          C.IsOutgoingChain H T → ∀ b : ℤ, T.shape = .finite 0 b →
          Disjoint D.closed_core C.carrier →
          (frontier (C.carrier ∪ (T.unionOpen : Set M)) ∩ D.core).Nonempty →
          ∃ tube : EpsilonTubeCertificate g ∅,
            tube.epsilon = C.epsilon ∧ HEq tube.chain T ∧
            tube.carrier = (T.unionOpen : Set M) ∧
            Nonempty (CapTubeAttachment C tube false) ∧
            ∃ a ∈ Ioo (0 : ℝ) 1, tube.cylinder.tail true a ⊆ D.carrier := by
  obtain ⟨ε₁, hε₁, hsmall, htails⟩ :=
    exists_finite_chain_opposite_attachment_tails_threshold.{u}
  obtain ⟨ε₂, hε₂, -, htube⟩ :=
    BalancedNeckChain.exists_finite_tubeCertificate_threshold.{u}
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, (min_le_left _ _).trans hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ g C D hε hDC H T hT b hshape hdis hcontact
  obtain ⟨tube, hεtube, hchain, hcarrier⟩ :=
    htube T (hε.trans (min_le_right _ _)) 0 b hshape ∅ (empty_subset _)
  obtain ⟨side, ⟨attachment⟩, a, ha, htail⟩ :=
    htails C D (hε.trans (min_le_left _ _)) hDC H T hT b hshape hdis hcontact tube hcarrier
  cases side
  · exact ⟨tube, hεtube, hchain, hcarrier, ⟨attachment⟩, a, ha, htail⟩
  · refine ⟨tube.reversedCylinder, hεtube, hchain, hcarrier,
      ⟨attachment.reversedCylinder⟩, 1 - a,
      ⟨by linarith [ha.2], by linarith [ha.1]⟩, ?_⟩
    change tube.cylinder.reversed.tail true (1 - a) ⊆ D.carrier
    rw [tube.cylinder.reversed_tail, sub_sub_cancel]
    exact htail

end CapCertificate

end PoincareConjecture
