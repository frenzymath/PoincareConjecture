import PoincareConjecture.Proofs.Horizon.Topology.MetricSpace.GromovHausdorff.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.MetricSpace.Gluing
import Mathlib.Topology.MetricSpace.Infsep

open Set Filter Topology
open scoped Topology

namespace Poincare.GromovHausdorff

universe u

structure FiniteDiameterBasedMetricSpace where
  carrier : Type u
  metric : MetricSpace carrier
  base : carrier
  finite_diameter : ∃ C : ℝ, ∀ p q : carrier,
    @dist carrier metric.toPseudoMetricSpace.toDist p q ≤ C

instance (X : FiniteDiameterBasedMetricSpace.{u}) : MetricSpace X.carrier := X.metric
instance (X : FiniteDiameterBasedMetricSpace.{u}) : Nonempty X.carrier := ⟨X.base⟩

def FiniteDiameterBasedMetricSpace.toBasedMetricSpaceBundle
    (X : FiniteDiameterBasedMetricSpace.{u}) : BasedMetricSpaceBundle.{u} :=
  { carrier := X.carrier
    metric := X.metric
    base := X.base }

structure PointedGHRealization
    (X Y : FiniteDiameterBasedMetricSpace.{u}) where
  ambient : BasedMetricSpaceBundle.{u}
  left : X.carrier → ambient.carrier
  right : Y.carrier → ambient.carrier
  left_isometry : Isometry left
  right_isometry : Isometry right
  left_base : left X.base = ambient.base
  right_base : right Y.base = ambient.base

private def pointedBaseMap
    (X : FiniteDiameterBasedMetricSpace.{u}) : Unit → X.carrier :=
  fun _ => X.base

private theorem pointedBaseMap_isometry
    (X : FiniteDiameterBasedMetricSpace.{u}) :
    Isometry (pointedBaseMap X) := by
  intro a b
  simp [pointedBaseMap]

noncomputable def basePointedGHRealization
    (X Y : FiniteDiameterBasedMetricSpace.{u}) :
    PointedGHRealization X Y := by
  let hX := pointedBaseMap_isometry X
  let hY := pointedBaseMap_isometry Y
  exact
    { ambient :=
        { carrier := Metric.GlueSpace hX hY
          metric := inferInstance
          base := Metric.toGlueL hX hY X.base }
      left := Metric.toGlueL hX hY
      right := Metric.toGlueR hX hY
      left_isometry := Metric.toGlueL_isometry hX hY
      right_isometry := Metric.toGlueR_isometry hX hY
      left_base := rfl
      right_base := (congrFun (Metric.toGlue_commute hX hY) ()).symm }

theorem nonempty_pointedGHRealization
    (X Y : FiniteDiameterBasedMetricSpace.{u}) :
    Nonempty (PointedGHRealization X Y) :=
  ⟨basePointedGHRealization X Y⟩

noncomputable def pointedHausdorffDist
    {X Y : FiniteDiameterBasedMetricSpace.{u}}
    (R : PointedGHRealization X Y) : ℝ :=
  @Metric.hausdorffDist R.ambient.carrier R.ambient.metric.toPseudoMetricSpace
    (Set.range R.left) (Set.range R.right)

theorem pointedHausdorffDist_nonneg
    {X Y : FiniteDiameterBasedMetricSpace.{u}}
    (R : PointedGHRealization X Y) :
    0 ≤ pointedHausdorffDist R := by
  exact Metric.hausdorffDist_nonneg

def pointedGHAdmissibleDistances
    (X Y : FiniteDiameterBasedMetricSpace.{u}) : Set ℝ :=
  Set.range (fun R : PointedGHRealization X Y => pointedHausdorffDist R)

noncomputable def pointedGHDistance
    (X Y : FiniteDiameterBasedMetricSpace.{u}) : ℝ :=
  sInf (pointedGHAdmissibleDistances X Y)

theorem pointedGHDistance_nonneg
    (X Y : FiniteDiameterBasedMetricSpace.{u}) :
    0 ≤ pointedGHDistance X Y := by
  apply Real.sInf_nonneg
  intro d hd
  rcases hd with ⟨R, rfl⟩
  exact pointedHausdorffDist_nonneg R

theorem pointedGHAdmissibleDistances_nonempty
    (X Y : FiniteDiameterBasedMetricSpace.{u}) :
    (pointedGHAdmissibleDistances X Y).Nonempty :=
  ⟨pointedHausdorffDist (basePointedGHRealization X Y),
    basePointedGHRealization X Y, rfl⟩

theorem pointedGHAdmissibleDistances_bddBelow
    (X Y : FiniteDiameterBasedMetricSpace.{u}) :
    BddBelow (pointedGHAdmissibleDistances X Y) := by
  refine ⟨0, ?_⟩
  intro d hd
  rcases hd with ⟨R, rfl⟩
  exact pointedHausdorffDist_nonneg R

theorem pointedGHDistance_le_realization
    {X Y : FiniteDiameterBasedMetricSpace.{u}}
    (R : PointedGHRealization X Y) :
    pointedGHDistance X Y ≤ pointedHausdorffDist R := by
  unfold pointedGHDistance pointedGHAdmissibleDistances
  exact csInf_le (pointedGHAdmissibleDistances_bddBelow X Y) ⟨R, rfl⟩

theorem pointedGHDistance_eq_realization_of_min
    {X Y : FiniteDiameterBasedMetricSpace.{u}}
    (R : PointedGHRealization X Y)
    (hmin : ∀ S : PointedGHRealization X Y,
      pointedHausdorffDist R ≤ pointedHausdorffDist S) :
    pointedGHDistance X Y = pointedHausdorffDist R := by
  apply le_antisymm
  · exact pointedGHDistance_le_realization R
  · unfold pointedGHDistance pointedGHAdmissibleDistances
    apply le_csInf (pointedGHAdmissibleDistances_nonempty X Y)
    rintro d ⟨S, rfl⟩
    exact hmin S

theorem pointedHausdorffDist_eq_zero_of_attained_zero
    {X Y : FiniteDiameterBasedMetricSpace.{u}}
    (R : PointedGHRealization X Y)
    (hattain : pointedGHDistance X Y = pointedHausdorffDist R)
    (hzero : pointedGHDistance X Y = 0) :
    pointedHausdorffDist R = 0 := by
  rw [← hattain, hzero]

theorem basedIsometry_of_realization_agreement
    {X Y : FiniteDiameterBasedMetricSpace.{u}}
    (R : PointedGHRealization X Y)
    (e : X.carrier ≃ᵢ Y.carrier)
    (hleft : ∀ x, R.left x = R.right (e x)) :
    e X.base = Y.base := by
  have hbase : R.right (e X.base) = R.right Y.base := by
    calc
      R.right (e X.base) = R.left X.base := (hleft X.base).symm
      _ = R.ambient.base := R.left_base
      _ = R.right Y.base := R.right_base.symm
  exact R.right_isometry.injective hbase

theorem basedIsometry_unique_of_realization_agreement
    {X Y : FiniteDiameterBasedMetricSpace.{u}}
    (R : PointedGHRealization X Y)
    (e₁ e₂ : X.carrier ≃ᵢ Y.carrier)
    (h₁ : ∀ x, R.left x = R.right (e₁ x))
    (h₂ : ∀ x, R.left x = R.right (e₂ x)) :
    e₁ = e₂ := by
  apply IsometryEquiv.ext
  intro x
  apply R.right_isometry.injective
  calc
    R.right (e₁ x) = R.left x := (h₁ x).symm
    _ = R.right (e₂ x) := h₂ x

theorem exists_pointedGHRealization_lt_add
    (X Y : FiniteDiameterBasedMetricSpace.{u})
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ R : PointedGHRealization X Y,
      pointedHausdorffDist R < pointedGHDistance X Y + epsilon := by
  have hlt : sInf (pointedGHAdmissibleDistances X Y) <
      sInf (pointedGHAdmissibleDistances X Y) + epsilon :=
    lt_add_of_pos_right _ hepsilon
  obtain ⟨d, hd, hdlt⟩ :=
    exists_lt_of_csInf_lt (pointedGHAdmissibleDistances_nonempty X Y) hlt
  rcases hd with ⟨R, rfl⟩
  exact ⟨R, hdlt⟩

theorem pointedGHDistance_eq_zero_iff_forall_pos_exists_realization_lt
    (X Y : FiniteDiameterBasedMetricSpace.{u}) :
    pointedGHDistance X Y = 0 ↔
      ∀ epsilon : ℝ, 0 < epsilon →
        ∃ R : PointedGHRealization X Y,
          pointedHausdorffDist R < epsilon := by
  constructor
  · intro hzero epsilon hepsilon
    obtain ⟨R, hR⟩ := exists_pointedGHRealization_lt_add X Y hepsilon
    refine ⟨R, ?_⟩
    rw [hzero] at hR
    simpa using hR
  · intro hreal
    apply le_antisymm
    · apply le_of_forall_pos_le_add
      intro epsilon hepsilon
      obtain ⟨R, hR⟩ := hreal epsilon hepsilon
      have hle : pointedGHDistance X Y ≤ epsilon :=
        (pointedGHDistance_le_realization R).trans (le_of_lt hR)
      linarith
    · exact pointedGHDistance_nonneg X Y

private theorem range_isBounded_of_finiteDiameter
    (X : FiniteDiameterBasedMetricSpace.{u})
    {A : Type u} [MetricSpace A] {f : X.carrier → A}
    (hf : Isometry f) :
    Bornology.IsBounded (Set.range f) := by
  rcases X.finite_diameter with ⟨C, hC⟩
  refine Metric.isBounded_iff.mpr ⟨C, ?_⟩
  rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
  rw [hf.dist_eq]
  exact hC x y

theorem pointedHausdorffEDist_ne_top
    {X Y : FiniteDiameterBasedMetricSpace.{u}}
    (R : PointedGHRealization X Y) :
    @Metric.hausdorffEDist R.ambient.carrier
      R.ambient.metric.toPseudoEMetricSpace
      (Set.range R.left) (Set.range R.right) ≠ ⊤ := by
  apply Metric.hausdorffEDist_ne_top_of_nonempty_of_bounded
  · exact Set.range_nonempty _
  · exact Set.range_nonempty _
  · exact range_isBounded_of_finiteDiameter X R.left_isometry
  · exact range_isBounded_of_finiteDiameter Y R.right_isometry

theorem exists_right_point_lt_of_pointedHausdorffDist_lt
    {X Y : FiniteDiameterBasedMetricSpace.{u}}
    (R : PointedGHRealization X Y) {epsilon : ℝ}
    (hε : pointedHausdorffDist R < epsilon) (x : X.carrier) :
    ∃ y : Y.carrier, dist (R.left x) (R.right y) < epsilon := by
  obtain ⟨y, hy, hdist⟩ :=
    Metric.exists_dist_lt_of_hausdorffDist_lt
      (show R.left x ∈ Set.range R.left from ⟨x, rfl⟩)
      hε (pointedHausdorffEDist_ne_top R)
  rcases hy with ⟨y, rfl⟩
  exact ⟨y, hdist⟩

theorem exists_left_point_lt_of_pointedHausdorffDist_lt
    {X Y : FiniteDiameterBasedMetricSpace.{u}}
    (R : PointedGHRealization X Y) {epsilon : ℝ}
    (hε : pointedHausdorffDist R < epsilon) (y : Y.carrier) :
    ∃ x : X.carrier, dist (R.left x) (R.right y) < epsilon := by
  obtain ⟨x, hx, hdist⟩ :=
    Metric.exists_dist_lt_of_hausdorffDist_lt'
      (show R.right y ∈ Set.range R.right from ⟨y, rfl⟩)
      hε (pointedHausdorffEDist_ne_top R)
  rcases hx with ⟨x, rfl⟩
  exact ⟨x, hdist⟩

theorem abs_dist_base_sub_dist_base_lt_of_corresponding
    {X Y : FiniteDiameterBasedMetricSpace.{u}}
    (R : PointedGHRealization X Y) {epsilon : ℝ}
    (x : X.carrier) (y : Y.carrier)
    (hxy : dist (R.left x) (R.right y) < epsilon) :
    |dist X.base x - dist Y.base y| < epsilon := by
  have hleft : dist X.base x = dist R.ambient.base (R.left x) := by
    rw [← R.left_base, R.left_isometry.dist_eq]
  have hright : dist Y.base y = dist R.ambient.base (R.right y) := by
    rw [← R.right_base, R.right_isometry.dist_eq]
  rw [hleft, hright]
  have hxy' : dist (R.right y) (R.left x) < epsilon := by
    simpa [dist_comm] using hxy
  have h₁ : dist R.ambient.base (R.left x) -
      dist R.ambient.base (R.right y) < epsilon := by
    have ht := dist_triangle R.ambient.base (R.right y) (R.left x)
    linarith
  have h₂ : -epsilon < dist R.ambient.base (R.left x) -
      dist R.ambient.base (R.right y) := by
    have ht := dist_triangle R.ambient.base (R.left x) (R.right y)
    linarith
  exact (abs_lt).2 ⟨h₂, h₁⟩

theorem exists_basedIsometry_of_attained_zero_of_compact_ranges
    {X Y : FiniteDiameterBasedMetricSpace.{u}}
    (R : PointedGHRealization X Y)
    (hleft : IsCompact (Set.range R.left))
    (hright : IsCompact (Set.range R.right))
    (hzero : pointedHausdorffDist R = 0) :
    ∃ e : X.carrier ≃ᵢ Y.carrier, e X.base = Y.base := by
  have hrange : Set.range R.left = Set.range R.right := by
    apply (IsClosed.hausdorffDist_zero_iff_eq hleft.isClosed hright.isClosed
      (pointedHausdorffEDist_ne_top R)).mp
    exact hzero
  let A : Set R.ambient.carrier := Set.range R.left
  let B : Set R.ambient.carrier := Set.range R.right
  have hAB : A = B := hrange
  let c : A ≃ᵢ B :=
    { toEquiv := Equiv.setCongr hAB
      isometry_toFun := by
        intro a b
        rfl }
  let eL : X.carrier ≃ᵢ A := R.left_isometry.isometryEquivOnRange
  let eR : B ≃ᵢ Y.carrier := R.right_isometry.isometryEquivOnRange.symm
  let e : X.carrier ≃ᵢ Y.carrier := eL.trans (c.trans eR)
  have hinter : ∀ x : X.carrier, R.left x = R.right (e x) := by
    intro x
    have hc : (c (eL x) : R.ambient.carrier) = (eL x : R.ambient.carrier) := by
      rfl
    have he : R.right (e x) = (c (eL x) : R.ambient.carrier) := by
      change R.right (eR (c (eL x))) = (c (eL x) : R.ambient.carrier)
      have hz := R.right_isometry.isometryEquivOnRange.apply_symm_apply
        (c (eL x))
      exact congrArg (fun z : B => (z : R.ambient.carrier)) hz
    have hl : (eL x : R.ambient.carrier) = R.left x := by
      rfl
    exact hl.symm.trans (hc.symm.trans he.symm)
  refine ⟨e, ?_⟩
  apply R.right_isometry.injective
  calc
    R.right (e X.base) = R.left X.base := (hinter X.base).symm
    _ = R.ambient.base := R.left_base
    _ = R.right Y.base := R.right_base.symm

theorem exists_basedIsometry_of_attained_zero_of_compact_carriers
    {X Y : FiniteDiameterBasedMetricSpace.{u}}
    [CompactSpace X.carrier] [CompactSpace Y.carrier]
    (R : PointedGHRealization X Y)
    (hattain : pointedGHDistance X Y = pointedHausdorffDist R)
    (hzero : pointedGHDistance X Y = 0) :
    ∃ e : X.carrier ≃ᵢ Y.carrier, e X.base = Y.base := by
  apply exists_basedIsometry_of_attained_zero_of_compact_ranges R
    (isCompact_range R.left_isometry.continuous)
    (isCompact_range R.right_isometry.continuous)
  exact pointedHausdorffDist_eq_zero_of_attained_zero R hattain hzero

noncomputable def PointedGHRealization.glue
    {X Y Z : FiniteDiameterBasedMetricSpace.{u}}
    (R : PointedGHRealization X Y)
    (S : PointedGHRealization Y Z) :
    PointedGHRealization X Z := by
  let hR := R.right_isometry
  let hS := S.left_isometry
  exact
    { ambient :=
        { carrier := Metric.GlueSpace hR hS
          metric := inferInstance
          base := Metric.toGlueL hR hS R.ambient.base }
      left := Metric.toGlueL hR hS ∘ R.left
      right := Metric.toGlueR hR hS ∘ S.right
      left_isometry := (Metric.toGlueL_isometry hR hS).comp R.left_isometry
      right_isometry := (Metric.toGlueR_isometry hR hS).comp S.right_isometry
      left_base := by
        change Metric.toGlueL hR hS (R.left X.base) =
          Metric.toGlueL hR hS R.ambient.base
        rw [R.left_base]
      right_base := by
        change Metric.toGlueR hR hS (S.right Z.base) =
          Metric.toGlueL hR hS R.ambient.base
        calc
          _ = Metric.toGlueR hR hS S.ambient.base := congrArg _ S.right_base
          _ = Metric.toGlueR hR hS (S.left Y.base) := congrArg _ S.left_base.symm
          _ = Metric.toGlueL hR hS (R.right Y.base) :=
            (congrFun (Metric.toGlue_commute hR hS) Y.base).symm
          _ = Metric.toGlueL hR hS R.ambient.base := congrArg _ R.right_base }

theorem pointedHausdorffDist_glue_le
    {X Y Z : FiniteDiameterBasedMetricSpace.{u}}
    (R : PointedGHRealization X Y)
    (S : PointedGHRealization Y Z) :
    pointedHausdorffDist (R.glue S) ≤
      pointedHausdorffDist R + pointedHausdorffDist S := by
  let hR := R.right_isometry
  let hS := S.left_isometry
  let eL := Metric.toGlueL hR hS
  let eR := Metric.toGlueR hR hS
  have heL : Isometry eL := Metric.toGlueL_isometry hR hS
  have heR : Isometry eR := Metric.toGlueR_isometry hR hS
  have hmidfun : eL ∘ R.right = eR ∘ S.left := Metric.toGlue_commute hR hS
  have hmid : Set.range (eL ∘ R.right) = Set.range (eR ∘ S.left) :=
    congrArg Set.range hmidfun
  have hxy : Metric.hausdorffDist (Set.range (eL ∘ R.left))
      (Set.range (eL ∘ R.right)) = pointedHausdorffDist R := by
    rw [Set.range_comp, Set.range_comp, Metric.hausdorffDist_image heL]
    rfl
  have hyz : Metric.hausdorffDist (Set.range (eL ∘ R.right))
      (Set.range (eR ∘ S.right)) = pointedHausdorffDist S := by
    rw [hmid, Set.range_comp, Set.range_comp, Metric.hausdorffDist_image heR]
    rfl
  have hfin : Metric.hausdorffEDist (Set.range (eL ∘ R.left))
      (Set.range (eL ∘ R.right)) ≠ ⊤ := by
    apply Metric.hausdorffEDist_ne_top_of_nonempty_of_bounded
    · exact Set.range_nonempty _
    · exact Set.range_nonempty _
    · exact range_isBounded_of_finiteDiameter X (heL.comp R.left_isometry)
    · exact range_isBounded_of_finiteDiameter Y (heL.comp R.right_isometry)
  unfold pointedHausdorffDist PointedGHRealization.glue
  dsimp only
  calc
    _ ≤ Metric.hausdorffDist (Set.range (eL ∘ R.left))
          (Set.range (eL ∘ R.right)) +
        Metric.hausdorffDist (Set.range (eL ∘ R.right))
          (Set.range (eR ∘ S.right)) := Metric.hausdorffDist_triangle hfin
    _ = _ := by
      rw [hxy, hyz]
      rfl

theorem pointedGHDistance_triangle
    (X Y Z : FiniteDiameterBasedMetricSpace.{u}) :
    pointedGHDistance X Z ≤
      pointedGHDistance X Y + pointedGHDistance Y Z := by
  apply le_of_forall_pos_le_add
  intro epsilon hepsilon
  obtain ⟨R, hR⟩ := exists_pointedGHRealization_lt_add X Y (half_pos hepsilon)
  obtain ⟨S, hS⟩ := exists_pointedGHRealization_lt_add Y Z (half_pos hepsilon)
  apply le_of_lt
  calc
    pointedGHDistance X Z ≤ pointedHausdorffDist (R.glue S) :=
      pointedGHDistance_le_realization (R.glue S)
    _ ≤ pointedHausdorffDist R + pointedHausdorffDist S :=
      pointedHausdorffDist_glue_le R S
    _ < (pointedGHDistance X Y + epsilon / 2) +
        (pointedGHDistance Y Z + epsilon / 2) := add_lt_add hR hS
    _ = pointedGHDistance X Y + pointedGHDistance Y Z + epsilon := by ring

def deltaNetModel
    (X : FiniteDiameterBasedMetricSpace.{u})
    (L : Set X.carrier) (hbase : X.base ∈ L) :
    FiniteDiameterBasedMetricSpace.{u} :=
  { carrier := L
    metric := inferInstance
    base := ⟨X.base, hbase⟩
    finite_diameter := by
      rcases X.finite_diameter with ⟨C, hC⟩
      refine ⟨C, ?_⟩
      intro p q
      exact hC p.1 q.1 }

theorem exists_finite_isDeltaNet_of_compactSpace
    {X : Type u} [MetricSpace X] [CompactSpace X]
    (δ : ℝ) (hδ : 0 < δ) (x : X) :
    ∃ L : Set X, L.Finite ∧ IsDeltaNet δ x L := by
  obtain ⟨t, htSub, htFinite, htCover⟩ :=
    (isCompact_univ : IsCompact (Set.univ : Set X)).finite_cover_balls hδ
  let L : Set X := insert x t
  have hLFinite : L.Finite := htFinite.insert x
  have hxL : x ∈ L := mem_insert x t
  have hLcover : ∀ y : X, ∃ z ∈ L, dist y z < δ := by
    intro y
    have hy : y ∈ ⋃ z ∈ t, Metric.ball z δ := htCover (mem_univ y)
    rcases Set.mem_iUnion.mp hy with ⟨z, hy⟩
    rcases Set.mem_iUnion.mp hy with ⟨hz, hyz⟩
    refine ⟨z, mem_insert_of_mem _ hz, ?_⟩
    simpa [Metric.mem_ball, dist_comm] using hyz
  letI : Fintype L := hLFinite.fintype
  by_cases hnontrivial : L.Nontrivial
  · obtain ⟨ε, hε, hsep⟩ := Set.relatively_discrete_of_finite (s := L)
    obtain ⟨u, hu, v, hv, huv⟩ := hnontrivial
    have hεtop : ε ≠ ⊤ := by
      intro htop
      have hle : (⊤ : ENNReal) ≤ edist u v := by
        simpa only [htop] using hsep u hu v hv huv
      exact edist_ne_top u v (top_unique hle)
    have hεreal : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' hεtop
    refine ⟨L, hLFinite, ⟨hxL, hLcover, ⟨ε.toReal, hεreal, ?_⟩⟩⟩
    intro u v hu hv huv
    have hle := hsep u hu v hv huv
    have hreal := ENNReal.toReal_mono (edist_ne_top u v) hle
    simpa [edist_dist] using hreal
  · have hsubsingleton : L.Subsingleton :=
      Set.not_nontrivial_iff.mp hnontrivial
    refine ⟨L, hLFinite, ⟨hxL, hLcover, ⟨1, zero_lt_one, ?_⟩⟩⟩
    intro u v hu hv huv
    exact (huv (hsubsingleton hu hv)).elim

theorem pointedGHDistance_le_deltaNet
    (X : FiniteDiameterBasedMetricSpace.{u})
    (δ : ℝ) (hδ : 0 ≤ δ) (L : Set X.carrier)
    (hL : IsDeltaNet δ X.base L) :
    pointedGHDistance X (deltaNetModel X L hL.1) ≤ δ := by
  let R : PointedGHRealization X (deltaNetModel X L hL.1) :=
    { ambient :=
        { carrier := X.carrier
          metric := X.metric
          base := X.base }
      left := id
      right := fun z => z.1
      left_isometry := isometry_id
      right_isometry := isometry_subtype_coe
      left_base := rfl
      right_base := rfl }
  have hR : pointedHausdorffDist R ≤ δ := by
    unfold pointedHausdorffDist
    apply Metric.hausdorffDist_le_of_mem_dist hδ
    · intro z hz
      rcases hz with ⟨z, rfl⟩
      rcases hL.2.1 z with ⟨w, hw, hzw⟩
      refine ⟨R.right ⟨w, hw⟩, ⟨⟨w, hw⟩, rfl⟩, ?_⟩
      exact le_of_lt hzw
    · intro z hz
      rcases hz with ⟨w, rfl⟩
      refine ⟨R.left w.1, ⟨w.1, rfl⟩, ?_⟩
      change dist w.1 w.1 ≤ δ
      simpa using hδ
  exact (pointedGHDistance_le_realization R).trans hR

theorem pointedGHDistance_symm
    (X Y : FiniteDiameterBasedMetricSpace.{u}) :
    pointedGHDistance X Y = pointedGHDistance Y X := by
  have hsets : pointedGHAdmissibleDistances X Y =
      pointedGHAdmissibleDistances Y X := by
    apply Set.Subset.antisymm
    · intro d hd
      rcases hd with ⟨R, rfl⟩
      let R' : PointedGHRealization Y X :=
        { ambient := R.ambient
          left := R.right
          right := R.left
          left_isometry := R.right_isometry
          right_isometry := R.left_isometry
          left_base := R.right_base
          right_base := R.left_base }
      refine ⟨R', ?_⟩
      simpa [pointedHausdorffDist, R'] using
        (Metric.hausdorffDist_comm (s := Set.range R.left)
          (t := Set.range R.right)).symm
    · intro d hd
      rcases hd with ⟨R, rfl⟩
      let R' : PointedGHRealization X Y :=
        { ambient := R.ambient
          left := R.right
          right := R.left
          left_isometry := R.right_isometry
          right_isometry := R.left_isometry
          left_base := R.right_base
          right_base := R.left_base }
      refine ⟨R', ?_⟩
      simpa [pointedHausdorffDist, R'] using
        (Metric.hausdorffDist_comm (s := Set.range R.left)
          (t := Set.range R.right)).symm
  unfold pointedGHDistance
  rw [hsets]

theorem pointedGHDistance_le_sum_deltaNets
    (X : FiniteDiameterBasedMetricSpace.{u})
    (δ₁ δ₂ : ℝ) (hδ₁ : 0 ≤ δ₁) (hδ₂ : 0 ≤ δ₂)
    (L₁ L₂ : Set X.carrier)
    (hL₁ : IsDeltaNet δ₁ X.base L₁)
    (hL₂ : IsDeltaNet δ₂ X.base L₂) :
    pointedGHDistance (deltaNetModel X L₁ hL₁.1)
      (deltaNetModel X L₂ hL₂.1) ≤ δ₁ + δ₂ := by
  calc
    pointedGHDistance (deltaNetModel X L₁ hL₁.1)
        (deltaNetModel X L₂ hL₂.1) ≤
        pointedGHDistance (deltaNetModel X L₁ hL₁.1) X +
          pointedGHDistance X (deltaNetModel X L₂ hL₂.1) :=
      pointedGHDistance_triangle _ _ _
    _ = pointedGHDistance X (deltaNetModel X L₁ hL₁.1) +
          pointedGHDistance X (deltaNetModel X L₂ hL₂.1) := by
      rw [pointedGHDistance_symm
        (deltaNetModel X L₁ hL₁.1) X]
    _ ≤ δ₁ + δ₂ := add_le_add
      (pointedGHDistance_le_deltaNet X δ₁ hδ₁ L₁ hL₁)
      (pointedGHDistance_le_deltaNet X δ₂ hδ₂ L₂ hL₂)

private def selfPointedGHRealization
    (X : FiniteDiameterBasedMetricSpace.{u}) :
    PointedGHRealization X X :=
  { ambient :=
      { carrier := X.carrier
        metric := X.metric
        base := X.base }
    left := id
    right := id
    left_isometry := isometry_id
    right_isometry := isometry_id
    left_base := rfl
    right_base := rfl }

theorem pointedGHDistance_self
    (X : FiniteDiameterBasedMetricSpace.{u}) :
    pointedGHDistance X X = 0 := by
  apply le_antisymm
  · let R := selfPointedGHRealization X
    have hR : pointedHausdorffDist R = 0 := by
      change @Metric.hausdorffDist X.carrier X.metric.toPseudoMetricSpace
        (Set.range (id : X.carrier → X.carrier))
        (Set.range (id : X.carrier → X.carrier)) = 0
      exact Metric.hausdorffDist_self_zero
        (s := Set.range (id : X.carrier → X.carrier))
    have hmem : pointedHausdorffDist R ∈ pointedGHAdmissibleDistances X X :=
      ⟨R, rfl⟩
    have hbounded : BddBelow (pointedGHAdmissibleDistances X X) := by
      refine ⟨0, ?_⟩
      intro d hd
      rcases hd with ⟨R', rfl⟩
      exact pointedHausdorffDist_nonneg R'
    exact hR ▸ csInf_le hbounded hmem
  · exact pointedGHDistance_nonneg X X

noncomputable def PointedCompactMetricSpace.toFiniteDiameterBasedMetricSpace
    (X : PointedCompactMetricSpace.{u}) :
    FiniteDiameterBasedMetricSpace.{u} := by
  letI : MetricSpace X.carrier := X.metric
  letI : CompactSpace X.carrier := X.compact
  letI : Nonempty X.carrier := X.nonempty
  have hbounded : Bornology.IsBounded (Set.univ : Set X.carrier) :=
    isCompact_univ.isBounded
  let C := Classical.choose (Metric.isBounded_iff.mp hbounded)
  have hC := Classical.choose_spec (Metric.isBounded_iff.mp hbounded)
  exact
    { carrier := X.carrier
      metric := X.metric
      base := X.base
      finite_diameter := ⟨C, fun p q => hC (mem_univ p) (mem_univ q)⟩ }

theorem pointedGHDistance_eq_zero_of_basedIsometry
    (X Y : FiniteDiameterBasedMetricSpace.{u})
    (e : X.carrier ≃ᵢ Y.carrier) (hbase : e X.base = Y.base) :
    pointedGHDistance X Y = 0 := by
  let R : PointedGHRealization X Y :=
    { ambient :=
        { carrier := Y.carrier
          metric := Y.metric
          base := Y.base }
      left := e
      right := id
      left_isometry := e.isometry
      right_isometry := isometry_id
      left_base := hbase
      right_base := rfl }
  have hR : pointedHausdorffDist R = 0 := by
    unfold pointedHausdorffDist
    rw [e.surjective.range_eq, Set.range_id]
    exact Metric.hausdorffDist_self_zero
  exact le_antisymm
    ((pointedGHDistance_le_realization R).trans_eq hR)
    (pointedGHDistance_nonneg _ _)

theorem pointedGHDistance_eq_ghDist_of_optimal_base_agreement
    {X Y : FiniteDiameterBasedMetricSpace.{u}}
    [CompactSpace X.carrier] [CompactSpace Y.carrier]
    (hbase :
      _root_.GromovHausdorff.optimalGHInjl X.carrier Y.carrier X.base =
        _root_.GromovHausdorff.optimalGHInjr X.carrier Y.carrier Y.base) :
    pointedGHDistance X Y =
      _root_.GromovHausdorff.ghDist X.carrier Y.carrier := by
  let R : PointedGHRealization X Y :=
    { ambient :=
        { carrier := _root_.GromovHausdorff.OptimalGHCoupling X.carrier Y.carrier
          metric := inferInstance
          base := _root_.GromovHausdorff.optimalGHInjl X.carrier Y.carrier X.base }
      left := _root_.GromovHausdorff.optimalGHInjl X.carrier Y.carrier
      right := _root_.GromovHausdorff.optimalGHInjr X.carrier Y.carrier
      left_isometry := _root_.GromovHausdorff.isometry_optimalGHInjl _ _
      right_isometry := _root_.GromovHausdorff.isometry_optimalGHInjr _ _
      left_base := rfl
      right_base := hbase.symm }
  have hR :
      pointedHausdorffDist R =
        _root_.GromovHausdorff.ghDist X.carrier Y.carrier := by
    change Metric.hausdorffDist
      (Set.range (_root_.GromovHausdorff.optimalGHInjl X.carrier Y.carrier))
      (Set.range (_root_.GromovHausdorff.optimalGHInjr X.carrier Y.carrier)) =
        _root_.GromovHausdorff.ghDist X.carrier Y.carrier
    exact _root_.GromovHausdorff.hausdorffDist_optimal
  have hupper : pointedGHDistance X Y ≤
      _root_.GromovHausdorff.ghDist X.carrier Y.carrier := by
    exact (pointedGHDistance_le_realization R).trans_eq hR
  have hlower : _root_.GromovHausdorff.ghDist X.carrier Y.carrier ≤
      pointedGHDistance X Y := by
    unfold pointedGHDistance
    apply le_csInf (pointedGHAdmissibleDistances_nonempty X Y)
    rintro d ⟨S, rfl⟩
    exact _root_.GromovHausdorff.ghDist_le_hausdorffDist
      S.left_isometry S.right_isometry
  exact le_antisymm hupper hlower

theorem exists_pointedGHRealization_attaining_of_optimal_base_agreement
    {X Y : FiniteDiameterBasedMetricSpace.{u}}
    [CompactSpace X.carrier] [CompactSpace Y.carrier]
    (hbase :
      _root_.GromovHausdorff.optimalGHInjl X.carrier Y.carrier X.base =
        _root_.GromovHausdorff.optimalGHInjr X.carrier Y.carrier Y.base) :
    ∃ R : PointedGHRealization X Y,
      pointedGHDistance X Y = pointedHausdorffDist R := by
  let R : PointedGHRealization X Y :=
    { ambient :=
        { carrier := _root_.GromovHausdorff.OptimalGHCoupling X.carrier Y.carrier
          metric := inferInstance
          base := _root_.GromovHausdorff.optimalGHInjl X.carrier Y.carrier X.base }
      left := _root_.GromovHausdorff.optimalGHInjl X.carrier Y.carrier
      right := _root_.GromovHausdorff.optimalGHInjr X.carrier Y.carrier
      left_isometry := _root_.GromovHausdorff.isometry_optimalGHInjl _ _
      right_isometry := _root_.GromovHausdorff.isometry_optimalGHInjr _ _
      left_base := rfl
      right_base := hbase.symm }
  have hR : pointedHausdorffDist R =
      _root_.GromovHausdorff.ghDist X.carrier Y.carrier := by
    change Metric.hausdorffDist
      (Set.range (_root_.GromovHausdorff.optimalGHInjl X.carrier Y.carrier))
      (Set.range (_root_.GromovHausdorff.optimalGHInjr X.carrier Y.carrier)) =
        _root_.GromovHausdorff.ghDist X.carrier Y.carrier
    exact _root_.GromovHausdorff.hausdorffDist_optimal
  exact ⟨R, (pointedGHDistance_eq_ghDist_of_optimal_base_agreement hbase).trans hR.symm⟩

theorem exists_basedIsometry_of_pointedGHDistance_eq_zero_of_optimal_base_agreement
    {X Y : FiniteDiameterBasedMetricSpace.{u}}
    [CompactSpace X.carrier] [CompactSpace Y.carrier]
    (hbase :
      _root_.GromovHausdorff.optimalGHInjl X.carrier Y.carrier X.base =
        _root_.GromovHausdorff.optimalGHInjr X.carrier Y.carrier Y.base)
    (hzero : pointedGHDistance X Y = 0) :
    ∃ e : X.carrier ≃ᵢ Y.carrier, e X.base = Y.base := by
  obtain ⟨R, hR⟩ :=
    exists_pointedGHRealization_attaining_of_optimal_base_agreement hbase
  exact exists_basedIsometry_of_attained_zero_of_compact_carriers R hR hzero

theorem pointedGHDistance_eq_zero_iff_basedIsometry_of_compact_carriers
    {X Y : FiniteDiameterBasedMetricSpace.{u}}
    [CompactSpace X.carrier] [CompactSpace Y.carrier]
    (hattain : ∃ R : PointedGHRealization X Y,
      pointedGHDistance X Y = pointedHausdorffDist R) :
    pointedGHDistance X Y = 0 ↔
      ∃ e : X.carrier ≃ᵢ Y.carrier, e X.base = Y.base := by
  constructor
  · intro hzero
    obtain ⟨R, hR⟩ := hattain
    exact exists_basedIsometry_of_attained_zero_of_compact_carriers
      R hR hzero
  · rintro ⟨e, hbase⟩
    exact pointedGHDistance_eq_zero_of_basedIsometry X Y e hbase

theorem pointedGHDistance_eq_zero_iff_basedIsometry_of_optimal_base_agreement
    {X Y : FiniteDiameterBasedMetricSpace.{u}}
    [CompactSpace X.carrier] [CompactSpace Y.carrier]
    (hbase :
      _root_.GromovHausdorff.optimalGHInjl X.carrier Y.carrier X.base =
        _root_.GromovHausdorff.optimalGHInjr X.carrier Y.carrier Y.base) :
    pointedGHDistance X Y = 0 ↔
      ∃ e : X.carrier ≃ᵢ Y.carrier, e X.base = Y.base := by
  constructor
  · exact exists_basedIsometry_of_pointedGHDistance_eq_zero_of_optimal_base_agreement
      hbase
  · rintro ⟨e, he⟩
    exact pointedGHDistance_eq_zero_of_basedIsometry X Y e he

def UniformlyBoundedDiameter
    (X : ℕ → FiniteDiameterBasedMetricSpace.{u}) : Prop :=
  ∃ C : ℝ, ∀ k (p q : (X k).carrier), dist p q ≤ C

def PointedGHConverges
    (X : ℕ → FiniteDiameterBasedMetricSpace.{u})
    (Y : FiniteDiameterBasedMetricSpace.{u}) : Prop :=
  UniformlyBoundedDiameter X ∧
    Tendsto (fun k => pointedGHDistance (X k) Y) atTop (𝓝 0)

theorem pointedGHDistance_eq_zero_of_common_pointedGH_limit
    (X : ℕ → FiniteDiameterBasedMetricSpace.{u})
    (Y Z : FiniteDiameterBasedMetricSpace.{u})
    (hY : PointedGHConverges X Y)
    (hZ : PointedGHConverges X Z) :
    pointedGHDistance Y Z = 0 := by
  have hupper : ∀ k : ℕ,
      pointedGHDistance Y Z ≤
        pointedGHDistance (X k) Y + pointedGHDistance (X k) Z := by
    intro k
    calc
      pointedGHDistance Y Z ≤
          pointedGHDistance Y (X k) + pointedGHDistance (X k) Z :=
        pointedGHDistance_triangle Y (X k) Z
      _ = pointedGHDistance (X k) Y + pointedGHDistance (X k) Z := by
        rw [pointedGHDistance_symm]
  have hsum : Tendsto
      (fun k => pointedGHDistance (X k) Y + pointedGHDistance (X k) Z)
      atTop (𝓝 0) := by
    simpa using hY.2.add hZ.2
  have hdist : Tendsto (fun _ : ℕ => pointedGHDistance Y Z)
      atTop (𝓝 0) :=
    squeeze_zero (fun _ => pointedGHDistance_nonneg Y Z) hupper hsum
  simpa using tendsto_nhds_unique_dist hdist tendsto_const_nhds

theorem exists_basedIsometry_of_common_pointedGH_limit_of_attained
    (X : ℕ → FiniteDiameterBasedMetricSpace.{u})
    (Y Z : FiniteDiameterBasedMetricSpace.{u})
    [CompactSpace Y.carrier] [CompactSpace Z.carrier]
    (hY : PointedGHConverges X Y)
    (hZ : PointedGHConverges X Z)
    (hattain : ∃ R : PointedGHRealization Y Z,
      pointedGHDistance Y Z = pointedHausdorffDist R) :
    ∃ e : Y.carrier ≃ᵢ Z.carrier, e Y.base = Z.base := by
  have hzero := pointedGHDistance_eq_zero_of_common_pointedGH_limit X Y Z hY hZ
  exact (pointedGHDistance_eq_zero_iff_basedIsometry_of_compact_carriers
    (X := Y) (Y := Z) hattain).mp hzero

noncomputable def realizationSequenceOfPointedGHConverges
    (X : ℕ → FiniteDiameterBasedMetricSpace.{u})
    (Y : FiniteDiameterBasedMetricSpace.{u})
    (h : PointedGHConverges X Y) :
    VaryingRealizationSequence
      (fun k => (X k).toBasedMetricSpaceBundle)
      Y.toBasedMetricSpaceBundle := by
  let epsilon : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1)
  have hepsilon_pos (k : ℕ) : 0 < epsilon k := by
    positivity
  let realization (k : ℕ) : PointedGHRealization (X k) Y :=
    Classical.choose (exists_pointedGHRealization_lt_add (X k) Y (hepsilon_pos k))
  have hrealization (k : ℕ) :
      pointedHausdorffDist (realization k) <
        pointedGHDistance (X k) Y + epsilon k :=
    Classical.choose_spec
      (exists_pointedGHRealization_lt_add (X k) Y (hepsilon_pos k))
  exact
    { ambient := fun k =>
        { carrier := (realization k).ambient.carrier
          metric := (realization k).ambient.metric }
      left := fun k => (realization k).left
      right := fun k => (realization k).right
      left_isometry := fun k => (realization k).left_isometry
      right_isometry := fun k => (realization k).right_isometry
      base_agree := fun k => by
        change (realization k).left (X k).base = (realization k).right Y.base
        exact (realization k).left_base.trans (realization k).right_base.symm
      hausdorff_tendsto_zero := by
        apply squeeze_zero
        · intro k
          exact Metric.hausdorffDist_nonneg
        · intro k
          exact le_of_lt (hrealization k)
        · simpa [epsilon] using
            h.2.add (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)) }

theorem pointedGHConverges_of_realizationSequence
    (X : ℕ → FiniteDiameterBasedMetricSpace.{u})
    (Y : FiniteDiameterBasedMetricSpace.{u})
    (hbounded : UniformlyBoundedDiameter X)
    (S : VaryingRealizationSequence
      (fun k => (X k).toBasedMetricSpaceBundle)
      Y.toBasedMetricSpaceBundle) :
    PointedGHConverges X Y := by
  refine ⟨hbounded, ?_⟩
  apply squeeze_zero
  · intro k
    exact pointedGHDistance_nonneg _ _
  · intro k
    let R : PointedGHRealization (X k) Y :=
      { ambient :=
          { carrier := (S.ambient k).carrier
            metric := (S.ambient k).metric
            base := S.left k (X k).base }
        left := S.left k
        right := S.right k
        left_isometry := S.left_isometry k
        right_isometry := S.right_isometry k
        left_base := rfl
        right_base := (S.base_agree k).symm }
    exact pointedGHDistance_le_realization R
  · exact S.hausdorff_tendsto_zero

theorem pointedGHConverges_iff_exists_realizationSequence
    (X : ℕ → FiniteDiameterBasedMetricSpace.{u})
    (Y : FiniteDiameterBasedMetricSpace.{u})
    (hbounded : UniformlyBoundedDiameter X) :
    PointedGHConverges X Y ↔
      ∃ S : VaryingRealizationSequence
        (fun k => (X k).toBasedMetricSpaceBundle)
        Y.toBasedMetricSpaceBundle,
        Tendsto (fun k => @Metric.hausdorffDist (S.ambient k).carrier inferInstance
          (Set.range (S.left k)) (Set.range (S.right k))) atTop (𝓝 0) := by
  constructor
  · intro h
    exact ⟨realizationSequenceOfPointedGHConverges X Y h, by
      exact (realizationSequenceOfPointedGHConverges X Y h).hausdorff_tendsto_zero⟩
  · rintro ⟨S, hS⟩
    exact pointedGHConverges_of_realizationSequence X Y hbounded S

def VaryingRealizationSequence.PointConverges
    {X : ℕ → BasedMetricSpaceBundle.{u}} {Y : BasedMetricSpaceBundle.{u}}
    (S : VaryingRealizationSequence X Y)
    (p : ∀ k, (X k).carrier) (q : Y.carrier) : Prop :=
    Tendsto (fun k => dist (S.left k (p k)) (S.right k q)) atTop (𝓝 0)

theorem VaryingRealizationSequence.tendsto_dist_base
    {X : ℕ → BasedMetricSpaceBundle.{u}} {Y : BasedMetricSpaceBundle.{u}}
    (S : VaryingRealizationSequence X Y)
    (p : ∀ k, (X k).carrier) (q : Y.carrier)
    (h : S.PointConverges p q) :
    Tendsto (fun k => dist ((X k).base) (p k)) atTop
      (𝓝 (dist Y.base q)) := by
  rw [tendsto_iff_dist_tendsto_zero]
  apply squeeze_zero (fun _ => dist_nonneg)
  · intro k
    have hleft :
        dist ((X k).base) (p k) =
          dist (S.right k Y.base) (S.left k (p k)) := by
      calc
        dist ((X k).base) (p k) =
            dist (S.left k ((X k).base)) (S.left k (p k)) :=
          ((S.left_isometry k).dist_eq _ _).symm
        _ = dist (S.right k Y.base) (S.left k (p k)) := by
          rw [S.base_agree k]
    have hright :
        dist Y.base q = dist (S.right k Y.base) (S.right k q) := by
      exact ((S.right_isometry k).dist_eq _ _).symm
    calc
      dist (dist ((X k).base) (p k)) (dist Y.base q) =
          dist (dist (S.right k Y.base) (S.left k (p k)))
            (dist (S.right k Y.base) (S.right k q)) := by
              rw [hleft, hright]
      _ ≤ dist (S.left k (p k)) (S.right k q) :=
        dist_dist_dist_le_right _ _ _
  · exact h

theorem VaryingRealizationSequence.eventually_mem_ball_of_pointConverges
    {X : ℕ → BasedMetricSpaceBundle.{u}} {Y : BasedMetricSpaceBundle.{u}}
    (S : VaryingRealizationSequence X Y)
    (p : ∀ k, (X k).carrier) (q : Y.carrier)
    (h : S.PointConverges p q) {r : ℝ} (hq : dist Y.base q < r) :
    ∀ᶠ k in atTop, p k ∈ Metric.ball (X k).base r := by
  have hdist := S.tendsto_dist_base p q h
  filter_upwards [hdist.eventually_lt_const hq] with k hk
  rw [Metric.mem_ball']
  exact hk

theorem VaryingRealizationSequence.eventually_dist_base_gt_of_pointConverges
    {X : ℕ → BasedMetricSpaceBundle.{u}} {Y : BasedMetricSpaceBundle.{u}}
    (S : VaryingRealizationSequence X Y)
    (p : ∀ k, (X k).carrier) (q : Y.carrier)
    (h : S.PointConverges p q) {r : ℝ} (hq : r < dist Y.base q) :
    ∀ᶠ k in atTop, r < dist ((X k).base) (p k) := by
  exact (S.tendsto_dist_base p q h).eventually_const_lt hq

theorem pointedGHDistance_le_varyingRealization
    (X : ℕ → FiniteDiameterBasedMetricSpace.{u})
    (Y : FiniteDiameterBasedMetricSpace.{u})
    (S : VaryingRealizationSequence
      (fun k => (X k).toBasedMetricSpaceBundle)
      Y.toBasedMetricSpaceBundle) (k : ℕ) :
    pointedGHDistance (X k) Y ≤
      @Metric.hausdorffDist (S.ambient k).carrier inferInstance
        (Set.range (S.left k)) (Set.range (S.right k)) := by
  let R : PointedGHRealization (X k) Y :=
    { ambient :=
        { carrier := (S.ambient k).carrier
          metric := (S.ambient k).metric
          base := S.left k (X k).base }
      left := S.left k
      right := S.right k
      left_isometry := S.left_isometry k
      right_isometry := S.right_isometry k
      left_base := rfl
      right_base := (S.base_agree k).symm }
  exact pointedGHDistance_le_realization R

theorem pointedGHDistance_tendsto_zero_of_varyingRealization
    (X : ℕ → FiniteDiameterBasedMetricSpace.{u})
    (Y : FiniteDiameterBasedMetricSpace.{u})
    (S : VaryingRealizationSequence
      (fun k => (X k).toBasedMetricSpaceBundle)
      Y.toBasedMetricSpaceBundle) :
    Tendsto (fun k => pointedGHDistance (X k) Y) atTop (𝓝 0) := by
  apply squeeze_zero
  · intro k
    exact pointedGHDistance_nonneg _ _
  · intro k
    exact pointedGHDistance_le_varyingRealization X Y S k
  · exact S.hausdorff_tendsto_zero

theorem pointedGHDistance_tendsto_zero_of_realizationSequence
    (X Y : FiniteDiameterBasedMetricSpace.{u})
    (S : RealizationSequence X.carrier Y.carrier X.base Y.base) :
    Tendsto (fun _ : ℕ => pointedGHDistance X Y) atTop (𝓝 0) := by
  have hle : ∀ k : ℕ, pointedGHDistance X Y ≤
      @Metric.hausdorffDist (S.ambient k).carrier inferInstance
        (Set.range (S.left k)) (Set.range (S.right k)) := by
    intro k
    let R : PointedGHRealization X Y :=
      { ambient :=
          { carrier := (S.ambient k).carrier
            metric := (S.ambient k).metric
            base := S.left k X.base }
        left := S.left k
        right := S.right k
        left_isometry := S.left_isometry k
        right_isometry := S.right_isometry k
        left_base := rfl
        right_base := (S.base_agree k).symm }
    exact pointedGHDistance_le_realization R
  apply squeeze_zero
  · intro k
    exact pointedGHDistance_nonneg _ _
  · intro k
    exact hle k
  · exact S.hausdorff_tendsto_zero

theorem pointedGHDistance_eq_zero_of_realizationSequence
    (X Y : FiniteDiameterBasedMetricSpace.{u})
    (S : RealizationSequence X.carrier Y.carrier X.base Y.base) :
    pointedGHDistance X Y = 0 := by
  have hconst := pointedGHDistance_tendsto_zero_of_realizationSequence X Y S
  simpa using tendsto_nhds_unique_dist hconst tendsto_const_nhds

def onePointFiniteDiameterBasedMetricSpace :
    FiniteDiameterBasedMetricSpace.{u} :=
  { carrier := PUnit
    metric := inferInstance
    base := PUnit.unit
    finite_diameter := ⟨0, by simp⟩ }

theorem pointedGHDistance_le_onePoint_of_diameterBound
    (X : FiniteDiameterBasedMetricSpace.{u}) (C : ℝ)
    (hC : ∀ p q : X.carrier, dist p q ≤ C) :
    pointedGHDistance X onePointFiniteDiameterBasedMetricSpace ≤ C := by
  have hC_nonneg : 0 ≤ C := by
    simpa using hC X.base X.base
  let R : PointedGHRealization X onePointFiniteDiameterBasedMetricSpace :=
    { ambient := X.toBasedMetricSpaceBundle
      left := id
      right := fun _ => X.base
      left_isometry := isometry_id
      right_isometry := by
        intro p q
        cases p
        cases q
        exact (edist_self X.base).trans
          (edist_self (PUnit.unit : onePointFiniteDiameterBasedMetricSpace.{u}.carrier)).symm
      left_base := rfl
      right_base := rfl }
  apply (pointedGHDistance_le_realization R).trans
  unfold pointedHausdorffDist
  apply Metric.hausdorffDist_le_of_mem_dist hC_nonneg
  · rintro z ⟨p, rfl⟩
    refine ⟨X.base, ⟨PUnit.unit, rfl⟩, hC p X.base⟩
  · rintro z ⟨p, rfl⟩
    refine ⟨X.base, ⟨X.base, rfl⟩, ?_⟩
    change dist X.base X.base ≤ C
    simpa using hC_nonneg

theorem pointedGHConverges_onePoint_of_diameter_tendsto
    (X : ℕ → FiniteDiameterBasedMetricSpace.{u})
    (diameterBound : ℕ → ℝ)
    (hbound : ∀ k (p q : (X k).carrier), dist p q ≤ diameterBound k)
    (htendsto : Tendsto diameterBound atTop (𝓝 0)) :
    PointedGHConverges X onePointFiniteDiameterBasedMetricSpace := by
  constructor
  · rcases htendsto.bddAbove_range with ⟨C, hC⟩
    refine ⟨C, fun k p q => (hbound k p q).trans ?_⟩
    exact hC ⟨k, rfl⟩
  · exact squeeze_zero
      (fun k => pointedGHDistance_nonneg _ _)
      (fun k => pointedGHDistance_le_onePoint_of_diameterBound
        (X k) (diameterBound k) (hbound k))
      htendsto

theorem pointedGHConverges_deltaNet
    (X : FiniteDiameterBasedMetricSpace.{u})
    (delta : ℕ → ℝ) (hdelta_nonneg : ∀ k, 0 ≤ delta k)
    (hdelta : Tendsto delta atTop (𝓝 0))
    (L : ℕ → Set X.carrier)
    (hL : ∀ k, IsDeltaNet (delta k) X.base (L k)) :
    PointedGHConverges
      (fun k => deltaNetModel X (L k) (hL k).1) X := by
  constructor
  · rcases X.finite_diameter with ⟨C, hC⟩
    exact ⟨C, fun k p q => hC p.1 q.1⟩
  · exact squeeze_zero
      (fun k => pointedGHDistance_nonneg _ _)
      (fun k => by
        rw [pointedGHDistance_symm]
        exact pointedGHDistance_le_deltaNet X (delta k) (hdelta_nonneg k) (L k) (hL k))
      hdelta

theorem exists_finite_deltaNet_approximation_of_compactSpace
    (X : FiniteDiameterBasedMetricSpace.{u}) [CompactSpace X.carrier] :
    ∃ delta : ℕ → ℝ, ∃ L : ℕ → Set X.carrier,
      Tendsto delta atTop (𝓝 0) ∧
      (∀ k, 0 < delta k) ∧
      ∃ hL : ∀ k, IsDeltaNet (delta k) X.base (L k),
        (∀ k, (L k).Finite) ∧
        PointedGHConverges
          (fun k => deltaNetModel X (L k) (hL k).1) X := by
  let delta : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1)
  have hdelta_pos (k : ℕ) : 0 < delta k := by
    simp only [delta]
    positivity
  have hdelta : Tendsto delta atTop (𝓝 0) := by
    simpa [delta] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  choose L hspec using fun k =>
    exists_finite_isDeltaNet_of_compactSpace
      (delta k) (hdelta_pos k) X.base
  let hL : ∀ k, IsDeltaNet (delta k) X.base (L k) :=
    fun k => (hspec k).2
  refine ⟨delta, L, hdelta, hdelta_pos, hL, ?_, ?_⟩
  · exact fun k => (hspec k).1
  · exact pointedGHConverges_deltaNet X delta
      (fun k => (hdelta_pos k).le) hdelta L hL

def ballModel (X : BasedMetricSpaceBundle.{u}) (r : ℝ) (hr : 0 < r) :
    FiniteDiameterBasedMetricSpace.{u} :=
  { carrier := Metric.ball X.base r
    metric := inferInstance
    base := ⟨X.base, Metric.mem_ball_self hr⟩
    finite_diameter := by
      refine ⟨2 * r, ?_⟩
      intro p q
      change dist p.1 q.1 ≤ 2 * r
      have hp := p.2
      have hq := q.2
      change dist p.1 X.base < r at hp
      change dist q.1 X.base < r at hq
      exact le_of_lt <| calc
        dist p.1 q.1 ≤ dist p.1 X.base + dist X.base q.1 := dist_triangle _ _ _
        _ < r + r := add_lt_add hp (by simpa [dist_comm] using hq)
        _ = 2 * r := by ring }

def ballModelInclusion
    (X : BasedMetricSpaceBundle.{u}) (r s : ℝ)
    (hr : 0 < r) (hs : 0 < s) (hrs : r ≤ s) :
    (ballModel X r hr).carrier → (ballModel X s hs).carrier :=
  fun p => ⟨p.1, lt_of_lt_of_le p.2 hrs⟩

theorem ballModelInclusion_isometry
    (X : BasedMetricSpaceBundle.{u}) (r s : ℝ)
    (hr : 0 < r) (hs : 0 < s) (hrs : r ≤ s) :
    Isometry (ballModelInclusion X r s hr hs hrs) := by
  intro p q
  rfl

theorem ballModelInclusion_base
    (X : BasedMetricSpaceBundle.{u}) (r s : ℝ)
    (hr : 0 < r) (hs : 0 < s) (hrs : r ≤ s) :
    ballModelInclusion X r s hr hs hrs (ballModel X r hr).base =
      (ballModel X s hs).base := by
  apply Subtype.ext
  rfl

noncomputable def ballModelNestedRealization
    (X : BasedMetricSpaceBundle.{u}) (r s : ℝ)
    (hr : 0 < r) (hs : 0 < s) (hrs : r ≤ s) :
    PointedGHRealization (ballModel X r hr) (ballModel X s hs) :=
  { ambient :=
      { carrier := (ballModel X s hs).carrier
        metric := inferInstance
        base := (ballModel X s hs).base }
    left := ballModelInclusion X r s hr hs hrs
    right := id
    left_isometry := ballModelInclusion_isometry X r s hr hs hrs
    right_isometry := isometry_id
    left_base := ballModelInclusion_base X r s hr hs hrs
    right_base := rfl }

theorem pointedHausdorffDist_ballModelNestedRealization_le
    (X : BasedMetricSpaceBundle.{u}) (r s : ℝ)
    (hr : 0 < r) (hs : 0 < s) (hrs : r ≤ s) :
    pointedHausdorffDist (ballModelNestedRealization X r s hr hs hrs) ≤ s := by
  unfold pointedHausdorffDist
  apply Metric.hausdorffDist_le_of_mem_dist (le_of_lt hs)
  · rintro z ⟨p, rfl⟩
    let ip := ballModelInclusion X r s hr hs hrs p
    refine ⟨ip, ⟨ip, rfl⟩, ?_⟩
    change dist ip ip ≤ s
    rw [dist_self]
    exact le_of_lt hs
  · rintro z ⟨p, rfl⟩
    let b : (ballModel X r hr).carrier := (ballModel X r hr).base
    refine ⟨ballModelInclusion X r s hr hs hrs b, ⟨b, rfl⟩, ?_⟩
    change dist p.1 X.base ≤ s
    have hp := p.2
    change dist p.1 X.base < s at hp
    exact hp.le

def PointedGHConvergesUnbounded
    (X : ℕ → BasedMetricSpaceBundle.{u})
    (Y : BasedMetricSpaceBundle.{u}) : Prop :=
  ∀ r : ℝ, ∀ hr : 0 < r,
    ∃ δ : ℕ → ℝ,
      Tendsto δ atTop (𝓝 0) ∧
      ∃ hpos : ∀ k, 0 < r + δ k,
        PointedGHConverges
          (fun k => ballModel (X k) (r + δ k) (hpos k))
          (ballModel Y r hr)

end Poincare.GromovHausdorff
