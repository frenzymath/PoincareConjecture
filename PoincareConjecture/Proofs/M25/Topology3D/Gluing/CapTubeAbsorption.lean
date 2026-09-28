import PoincareConjecture.Proofs.M25.Topology3D.Gluing.ClosedModelCapData
import PoincareConjecture.Proofs.M25.Topology3D.Space3.ChartUnion








set_option autoImplicit false
open Set
open scoped Manifold ContDiff
universe u
namespace PoincareConjecture.M25.Topology3D




structure CapTubeChartExtension
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
    [T3Space M] {g : RiemannianMetric 3 M} {X : Set M}
    (cap : ClosedModelCapData g) (tube : EpsilonTubeCertificate g X) where
  cap_chart : OpenPartialHomeomorph RoundCylinderSpace M
  tube_chart : OpenPartialHomeomorph RoundCylinderSpace M
  cap_chart_source : cap_chart.source ⊆
    univ ×ˢ Ioo (-cap.epsilon⁻¹) cap.epsilon⁻¹
  tube_chart_source : tube_chart.source ⊆
    univ ×ˢ Ioo (-cap.epsilon⁻¹) cap.epsilon⁻¹
  source_cover : cap_chart.source ∪ tube_chart.source =
    univ ×ˢ Ioo (-cap.epsilon⁻¹) cap.epsilon⁻¹
  cap_chart_target_subset : cap_chart.target ⊆ cap.carrier
  tube_chart_target_subset : tube_chart.target ⊆ tube.carrier
  compatible : EqOn cap_chart tube_chart
    (cap_chart.source ∩ tube_chart.source)
  inverse_compatible : EqOn cap_chart.symm tube_chart.symm
    (cap_chart.target ∩ tube_chart.target)
  cap_chart_smooth : ContMDiffOn
    ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ cap_chart cap_chart.source
  tube_chart_smooth : ContMDiffOn
    ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ tube_chart tube_chart.source
  cap_chart_inverse_smooth : ContMDiffOn
    (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ cap_chart.symm cap_chart.target
  tube_chart_inverse_smooth : ContMDiffOn
    (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ tube_chart.symm tube_chart.target
namespace CapTubeChartExtension
variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T3Space M] {g : RiemannianMetric 3 M} {X : Set M}
  {cap : ClosedModelCapData g} {tube : EpsilonTubeCertificate g X}

noncomputable def glued (H : CapTubeChartExtension cap tube) :
    OpenPartialHomeomorph RoundCylinderSpace M :=
  glueOpenCharts H.cap_chart H.tube_chart H.compatible H.inverse_compatible
@[simp] theorem glued_source (H : CapTubeChartExtension cap tube) :
    (H.glued).source =
      univ ×ˢ Ioo (-cap.epsilon⁻¹) cap.epsilon⁻¹ := by
  rw [glued, glueOpenCharts_source, H.source_cover]
theorem glued_target (H : CapTubeChartExtension cap tube) :
    (H.glued).target = H.cap_chart.target ∪ H.tube_chart.target := by
  rw [glued, glueOpenCharts_target]
theorem glued_target_subset (H : CapTubeChartExtension cap tube) :
    (H.glued).target ⊆ cap.carrier ∪ tube.carrier := by
  rw [H.glued_target]
  intro x hx
  rcases hx with hx | hx
  · exact Or.inl (H.cap_chart_target_subset hx)
  · exact Or.inr (H.tube_chart_target_subset hx)
theorem glued_smooth (H : CapTubeChartExtension cap tube) :
    ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ H.glued H.glued.source := by
  have h := (H.cap_chart_smooth.congr
      (glueOpenCharts_eqOn_left H.cap_chart H.tube_chart
      H.compatible H.inverse_compatible)).union_of_isOpen
    (H.tube_chart_smooth.congr
      (glueOpenCharts_eqOn_right H.cap_chart H.tube_chart
      H.compatible H.inverse_compatible))
    H.cap_chart.open_source H.tube_chart.open_source
  simpa only [glued, glueOpenCharts_source, H.source_cover] using h
theorem glued_inverse_smooth (H : CapTubeChartExtension cap tube) :
    ContMDiffOn (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ H.glued.symm H.glued.target := by
  have h := (H.cap_chart_inverse_smooth.congr
      (glueOpenCharts_symm_eqOn_left H.cap_chart H.tube_chart
      H.compatible H.inverse_compatible)).union_of_isOpen
    (H.tube_chart_inverse_smooth.congr
      (glueOpenCharts_symm_eqOn_right H.cap_chart H.tube_chart
      H.compatible H.inverse_compatible))
    H.cap_chart.open_target H.tube_chart.open_target
  simpa only [glued, glueOpenCharts_target] using h
end CapTubeChartExtension



structure CapTubeAbsorptionData
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
    [T3Space M] {g : RiemannianMetric 3 M} {X : Set M}
    (cap : ClosedModelCapData g) (tube : EpsilonTubeCertificate g X) where
  chart : CapTubeChartExtension cap tube
  carrier_open : IsOpen (cap.carrier ∪ tube.carrier)
  puncture : RealProjectiveThree
  puncture_eq : puncture = cap.puncture
  model_equivalence :
    CapModelEquivalence cap.model_kind puncture (cap.carrier ∪ tube.carrier)
  closed_core : Set M
  closed_core_compact : IsCompact closed_core
  closed_core_eq_complement_end :
    closed_core = (cap.carrier ∪ tube.carrier) \ chart.glued.target
  compact_tail_complement : ∀ s ∈ Ioo (-cap.epsilon⁻¹) cap.epsilon⁻¹,
    IsCompact ((cap.carrier ∪ tube.carrier) \
      chart.glued.cylinderTail cap.epsilon⁻¹ s)
  cut_topology : ∀ s ∈ Ioo (-cap.epsilon⁻¹) cap.epsilon⁻¹,
    let T := chart.glued.cylinderTail cap.epsilon⁻¹ s
    let K := (cap.carrier ∪ tube.carrier) \ T
    let V := closed_core ∪ chart.glued ''
      (univ ×ˢ Ioo (-cap.epsilon⁻¹) s)
    let S := chart.glued '' (univ ×ˢ ({s} : Set ℝ))
    K ⊆ (cap.carrier ∪ tube.carrier) ∧ IsOpen V ∧ closure V = K ∧
      interior K = V ∧ frontier V = S ∧ frontier K = S ∧
      frontier (cap.carrier ∪ tube.carrier) ⊆ closure T
  core : Set M
  core_nonempty : core.Nonempty
  core_subset_closed_core : core ⊆ closed_core
  carrier_connected : IsConnected (cap.carrier ∪ tube.carrier)
namespace CapTubeAbsorptionData
variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T3Space M] {g : RiemannianMetric 3 M} {X : Set M}
  {cap : ClosedModelCapData g} {tube : EpsilonTubeCertificate g X}


noncomputable def toClosedModelCapData
    (D : CapTubeAbsorptionData cap tube) : ClosedModelCapData g :=
  { epsilon := cap.epsilon
    epsilon_pos := cap.epsilon_pos
    carrier := cap.carrier ∪ tube.carrier
    carrier_open := D.carrier_open
    puncture := D.puncture
    model_kind := cap.model_kind
    model_equivalence := D.model_equivalence
    end_chart := D.chart.glued
    end_chart_source := D.chart.glued_source
    end_chart_target_subset := D.chart.glued_target_subset
    end_chart_smooth := D.chart.glued_smooth
    end_chart_inverse_smooth := D.chart.glued_inverse_smooth
    closed_core := D.closed_core
    closed_core_compact := D.closed_core_compact
    closed_core_eq_complement_end := D.closed_core_eq_complement_end
    compact_tail_complement := D.compact_tail_complement
    cut_topology := D.cut_topology
    core := D.core
    core_nonempty := D.core_nonempty
    core_subset_closed_core := D.core_subset_closed_core
    carrier_connected := D.carrier_connected }
theorem toClosedModelCapData_carrier
    (D : CapTubeAbsorptionData cap tube) :
    (D.toClosedModelCapData).carrier = cap.carrier ∪ tube.carrier := rfl
theorem toClosedModelCapData_model_kind
    (D : CapTubeAbsorptionData cap tube) :
    (D.toClosedModelCapData).model_kind = cap.model_kind := rfl
theorem toClosedModelCapData_puncture
    (D : CapTubeAbsorptionData cap tube) :
    (D.toClosedModelCapData).puncture = cap.puncture := D.puncture_eq
end CapTubeAbsorptionData



noncomputable def ClosedModelCapData.absorb_tube
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
    [T3Space M] {g : RiemannianMetric 3 M} {X : Set M}
    (_hS : SchoenfliesService) (_hD : DiffSphereIsotopyService)
    (cap : ClosedModelCapData g) (tube : EpsilonTubeCertificate g X)
    (side : Bool) (_attachment : ClosedModelCapTubeAttachment cap tube side)
    (D : CapTubeAbsorptionData cap tube) : ClosedModelCapData g :=
  D.toClosedModelCapData
theorem ClosedModelCapData.absorb_tube_carrier
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
    [T3Space M] {g : RiemannianMetric 3 M} {X : Set M}
    (hS : SchoenfliesService) (hD : DiffSphereIsotopyService)
    (cap : ClosedModelCapData g) (tube : EpsilonTubeCertificate g X)
    (side : Bool) (attachment : ClosedModelCapTubeAttachment cap tube side)
    (D : CapTubeAbsorptionData cap tube) :
    (cap.absorb_tube hS hD tube side attachment D).carrier =
      cap.carrier ∪ tube.carrier :=
  CapTubeAbsorptionData.toClosedModelCapData_carrier D
theorem ClosedModelCapData.absorb_tube_model_kind
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
    [T3Space M] {g : RiemannianMetric 3 M} {X : Set M}
    (hS : SchoenfliesService) (hD : DiffSphereIsotopyService)
    (cap : ClosedModelCapData g) (tube : EpsilonTubeCertificate g X)
    (side : Bool) (attachment : ClosedModelCapTubeAttachment cap tube side)
    (D : CapTubeAbsorptionData cap tube) :
    (cap.absorb_tube hS hD tube side attachment D).model_kind = cap.model_kind :=
  CapTubeAbsorptionData.toClosedModelCapData_model_kind D
theorem ClosedModelCapData.absorb_tube_puncture
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
    [T3Space M] {g : RiemannianMetric 3 M} {X : Set M}
    (hS : SchoenfliesService) (hD : DiffSphereIsotopyService)
    (cap : ClosedModelCapData g) (tube : EpsilonTubeCertificate g X)
    (side : Bool) (attachment : ClosedModelCapTubeAttachment cap tube side)
    (D : CapTubeAbsorptionData cap tube) :
    (cap.absorb_tube hS hD tube side attachment D).puncture = cap.puncture :=
  CapTubeAbsorptionData.toClosedModelCapData_puncture D

structure CollarShrinkData
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
    [T3Space M] {g : RiemannianMetric 3 M} {X : Set M}
    (cap : ClosedModelCapData g) (tube : EpsilonTubeCertificate g X)
    (side : Bool) where
  a : ℝ
  a_mem : a ∈ Ioo (0 : ℝ) 1
  tail_subset : tube.cylinder.tail side a ⊆ cap.carrier
  overlap_subset : cap.carrier ∩ tube.carrier ⊆ tube.cylinder.tail side a
  Φ : OpenPartialHomeomorph M M
  source_eq : Φ.source = cap.carrier ∪ tube.carrier
  target_eq : Φ.target = cap.carrier
  smooth : ContMDiffOn (𝓡 3) (𝓡 3) ∞ Φ (cap.carrier ∪ tube.carrier)
  symm_smooth : ContMDiffOn (𝓡 3) (𝓡 3) ∞ Φ.symm cap.carrier
  eq_id : ∀ x, x ∉ tube.carrier → Φ x = x
  image_tube : Φ '' tube.carrier = tube.cylinder.tail side a
namespace CollarShrinkData
variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T3Space M] {g : RiemannianMetric 3 M} {X : Set M}
  {cap : ClosedModelCapData g} {tube : EpsilonTubeCertificate g X}
  {side : Bool} (S : CollarShrinkData cap tube side)
theorem map_mem {x : M} (hx : x ∈ cap.carrier ∪ tube.carrier) :
    S.Φ x ∈ cap.carrier := by
  rw [← S.target_eq]
  exact S.Φ.map_source (by rw [S.source_eq]; exact hx)
theorem symm_mem {y : M} (hy : y ∈ cap.carrier) :
    S.Φ.symm y ∈ cap.carrier ∪ tube.carrier := by
  rw [← S.source_eq]
  exact S.Φ.map_target (by rw [S.target_eq]; exact hy)
theorem symm_apply_apply {x : M} (hx : x ∈ cap.carrier ∪ tube.carrier) :
    S.Φ.symm (S.Φ x) = x :=
  S.Φ.left_inv (by rw [S.source_eq]; exact hx)
theorem apply_symm_apply {y : M} (hy : y ∈ cap.carrier) :
    S.Φ (S.Φ.symm y) = y :=
  S.Φ.right_inv (by rw [S.target_eq]; exact hy)
theorem symm_image_carrier :
    S.Φ.symm '' cap.carrier = cap.carrier ∪ tube.carrier := by
  rw [← S.source_eq, ← S.Φ.symm_image_target_eq_source, S.target_eq]
theorem symm_image_diff {A : Set M} (hA : A ⊆ cap.carrier) :
    S.Φ.symm '' (cap.carrier \ A) =
      (cap.carrier ∪ tube.carrier) \ S.Φ.symm '' A := by
  apply Subset.antisymm
  · rintro y ⟨x, hx, rfl⟩
    refine ⟨S.symm_mem (hx.1), ?_⟩
    intro hy
    rcases hy with ⟨z, hz, hzy⟩
    have hz' : z ∈ cap.carrier := hA hz
    have heq : z = x := by
      have h := congrArg S.Φ hzy
      rw [S.apply_symm_apply hz', S.apply_symm_apply hx.1] at h
      exact h
    exact hx.2 (heq ▸ hz)
  · rintro y ⟨hy, hyA⟩
    have hycap : S.Φ y ∈ cap.carrier := S.map_mem hy
    refine ⟨S.Φ y, ⟨hycap, ?_⟩, ?_⟩
    · intro h
      apply hyA
      refine ⟨S.Φ y, h, ?_⟩
      exact S.symm_apply_apply hy
    · exact S.symm_apply_apply hy
noncomputable def extendedChart : OpenPartialHomeomorph RoundCylinderSpace M :=
  cap.end_chart.trans S.Φ.symm
theorem extendedChart_source :
    S.extendedChart.source = univ ×ˢ Ioo (-cap.epsilon⁻¹) cap.epsilon⁻¹ := by
  rw [extendedChart, OpenPartialHomeomorph.trans_source,
    OpenPartialHomeomorph.symm_source, S.target_eq, ← cap.end_chart_source]
  apply inter_eq_left.2
  intro z hz
  exact cap.end_chart_target_subset (cap.end_chart.map_source hz)
theorem extendedChart_target :
    S.extendedChart.target = S.Φ.symm '' cap.end_chart.target := by
  rw [← S.extendedChart.image_source_eq_target, S.extendedChart_source,
    ← cap.end_chart_source, ← cap.end_chart.image_source_eq_target, ← image_comp]
  rfl
theorem extendedChart_apply (z : RoundCylinderSpace) :
    S.extendedChart z = S.Φ.symm (cap.end_chart z) := rfl
theorem extendedChart_target_subset :
    S.extendedChart.target ⊆ cap.carrier ∪ tube.carrier := by
  rw [S.extendedChart_target]
  rintro y ⟨w, hw, rfl⟩
  exact S.symm_mem (cap.end_chart_target_subset hw)
theorem extendedChart_smooth :
    ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞
      S.extendedChart S.extendedChart.source := by
  rw [S.extendedChart_source]
  have h := S.symm_smooth.comp cap.end_chart_smooth
    (fun z hz => by
      exact cap.end_chart_target_subset (cap.end_chart.map_source hz))
  simpa only [extendedChart, OpenPartialHomeomorph.coe_trans,
    cap.end_chart_source, Function.comp_def] using h
theorem extendedChart_symm_smooth :
    ContMDiffOn (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞
      S.extendedChart.symm S.extendedChart.target := by
  have hΦ : ContMDiffOn (𝓡 3) (𝓡 3) ∞ S.Φ S.extendedChart.target :=
    S.smooth.mono (by
      intro x hx
      rw [extendedChart, OpenPartialHomeomorph.trans_target] at hx
      rw [← S.source_eq]
      exact hx.1)
  have h := cap.end_chart_inverse_smooth.comp hΦ
    (fun x hx => by
      rw [extendedChart, OpenPartialHomeomorph.trans_target] at hx
      exact hx.2)
  simpa only [extendedChart, OpenPartialHomeomorph.coe_trans_symm,
    OpenPartialHomeomorph.symm_symm, Function.comp_def] using h
theorem isOpen_capPiece :
    IsOpen (S.extendedChart.source ∩ S.extendedChart ⁻¹' cap.carrier) :=
  S.extendedChart.isOpen_inter_preimage cap.carrier_open
theorem isOpen_tubePiece :
    IsOpen (S.extendedChart.source ∩ S.extendedChart ⁻¹' tube.carrier) :=
  S.extendedChart.isOpen_inter_preimage tube.carrier_open
noncomputable def chartExtension : CapTubeChartExtension cap tube where
  cap_chart := S.extendedChart.restrOpen _ S.isOpen_capPiece
  tube_chart := S.extendedChart.restrOpen _ S.isOpen_tubePiece
  cap_chart_source := by
    rw [OpenPartialHomeomorph.restrOpen_source, ← S.extendedChart_source]
    exact inter_subset_left
  tube_chart_source := by
    rw [OpenPartialHomeomorph.restrOpen_source, ← S.extendedChart_source]
    exact inter_subset_left
  source_cover := by
    rw [OpenPartialHomeomorph.restrOpen_source, OpenPartialHomeomorph.restrOpen_source,
      ← S.extendedChart_source]
    apply Subset.antisymm
    · exact union_subset inter_subset_left inter_subset_left
    · intro z hz
      rcases S.extendedChart_target_subset (S.extendedChart.map_source hz) with h | h
      · exact Or.inl ⟨hz, hz, h⟩
      · exact Or.inr ⟨hz, hz, h⟩
  cap_chart_target_subset := by
    rw [← OpenPartialHomeomorph.image_source_eq_target, OpenPartialHomeomorph.restrOpen_source]
    rintro y ⟨z, ⟨_, _, hz⟩, rfl⟩
    exact hz
  tube_chart_target_subset := by
    rw [← OpenPartialHomeomorph.image_source_eq_target, OpenPartialHomeomorph.restrOpen_source]
    rintro y ⟨z, ⟨_, _, hz⟩, rfl⟩
    exact hz
  compatible := fun _ _ => rfl
  inverse_compatible := fun _ _ => rfl
  cap_chart_smooth := by
    rw [OpenPartialHomeomorph.restrOpen_source]
    exact S.extendedChart_smooth.mono inter_subset_left
  tube_chart_smooth := by
    rw [OpenPartialHomeomorph.restrOpen_source]
    exact S.extendedChart_smooth.mono inter_subset_left
  cap_chart_inverse_smooth := by
    apply S.extendedChart_symm_smooth.mono
    rw [← OpenPartialHomeomorph.image_source_eq_target, OpenPartialHomeomorph.restrOpen_source,
      ← S.extendedChart.image_source_eq_target]
    exact image_mono inter_subset_left
  tube_chart_inverse_smooth := by
    apply S.extendedChart_symm_smooth.mono
    rw [← OpenPartialHomeomorph.image_source_eq_target, OpenPartialHomeomorph.restrOpen_source,
      ← S.extendedChart.image_source_eq_target]
    exact image_mono inter_subset_left
theorem glued_eq :
    EqOn S.chartExtension.glued S.extendedChart S.extendedChart.source ∧
    S.chartExtension.glued.target = S.extendedChart.target := by
  constructor
  · intro z hz
    have hz' : z ∈ S.chartExtension.cap_chart.source ∪
        S.chartExtension.tube_chart.source := by
      rw [S.chartExtension.source_cover]
      simpa only [S.extendedChart_source] using hz
    rcases hz' with hz' | hz'
    · exact glueOpenCharts_eqOn_left _ _ _ _ hz'
    · exact glueOpenCharts_eqOn_right _ _ _ _ hz'
  · rw [CapTubeChartExtension.glued_target]
    apply Set.Subset.antisymm
    · intro y hy
      rcases hy with hy | hy
      · rw [← S.extendedChart.image_source_eq_target]
        have hz := S.chartExtension.cap_chart.map_target hy
        refine ⟨S.chartExtension.cap_chart.symm y, ?_, ?_⟩
        · change S.chartExtension.cap_chart.symm y ∈
            (S.extendedChart.restrOpen _ S.isOpen_capPiece).source at hz
          rw [OpenPartialHomeomorph.restrOpen_source] at hz
          exact hz.1
        · calc
            S.extendedChart (S.chartExtension.cap_chart.symm y) =
                S.chartExtension.cap_chart (S.chartExtension.cap_chart.symm y) := by
              change S.extendedChart (S.chartExtension.cap_chart.symm y) =
                (S.extendedChart.restrOpen _ S.isOpen_capPiece)
                  (S.chartExtension.cap_chart.symm y)
              rfl
            _ = y := S.chartExtension.cap_chart.right_inv hy
      · rw [← S.extendedChart.image_source_eq_target]
        have hz := S.chartExtension.tube_chart.map_target hy
        refine ⟨S.chartExtension.tube_chart.symm y, ?_, ?_⟩
        · change S.chartExtension.tube_chart.symm y ∈
            (S.extendedChart.restrOpen _ S.isOpen_tubePiece).source at hz
          rw [OpenPartialHomeomorph.restrOpen_source] at hz
          exact hz.1
        · calc
            S.extendedChart (S.chartExtension.tube_chart.symm y) =
                S.chartExtension.tube_chart (S.chartExtension.tube_chart.symm y) := by
              change S.extendedChart (S.chartExtension.tube_chart.symm y) =
                (S.extendedChart.restrOpen _ S.isOpen_tubePiece)
                  (S.chartExtension.tube_chart.symm y)
              rfl
            _ = y := S.chartExtension.tube_chart.right_inv hy
    · intro y hy
      rcases S.extendedChart_target_subset hy with hycap | hytube
      · apply Or.inl
        rw [← S.chartExtension.cap_chart.image_source_eq_target]
        refine ⟨S.extendedChart.symm y, ?_, ?_⟩
        · change S.extendedChart.symm y ∈
            (S.extendedChart.restrOpen _ S.isOpen_capPiece).source
          rw [OpenPartialHomeomorph.restrOpen_source]
          exact ⟨S.extendedChart.map_target hy,
            S.extendedChart.map_target hy, by
              change S.extendedChart (S.extendedChart.symm y) ∈ cap.carrier
              rw [S.extendedChart.right_inv hy]
              exact hycap⟩
        · exact S.extendedChart.right_inv hy
      · apply Or.inr
        rw [← S.chartExtension.tube_chart.image_source_eq_target]
        refine ⟨S.extendedChart.symm y, ?_, ?_⟩
        · change S.extendedChart.symm y ∈
            (S.extendedChart.restrOpen _ S.isOpen_tubePiece).source
          rw [OpenPartialHomeomorph.restrOpen_source]
          exact ⟨S.extendedChart.map_target hy,
            S.extendedChart.map_target hy, by
              change S.extendedChart (S.extendedChart.symm y) ∈ tube.carrier
              rw [S.extendedChart.right_inv hy]
              exact hytube⟩
        · exact S.extendedChart.right_inv hy
theorem glued_cylinderTail {s : ℝ} (hs : s ∈ Ioo (-cap.epsilon⁻¹) cap.epsilon⁻¹) :
    S.chartExtension.glued.cylinderTail cap.epsilon⁻¹ s =
      S.Φ.symm '' (cap.end_chart.cylinderTail cap.epsilon⁻¹ s) := by
  unfold OpenPartialHomeomorph.cylinderTail
  have hsub : (univ : Set UnitTwoSphere) ×ˢ Ioo s cap.epsilon⁻¹ ⊆
      S.extendedChart.source := by
    rw [S.extendedChart_source]
    exact prod_mono_right (Ioo_subset_Ioo hs.1.le le_rfl)
  rw [Set.EqOn.image_eq (Set.EqOn.mono hsub (S.glued_eq).1), ← image_comp]
  rfl
theorem cut_topology_transport (s : ℝ)
    (hs : s ∈ Ioo (-cap.epsilon⁻¹) cap.epsilon⁻¹) :
    let T := S.chartExtension.glued.cylinderTail cap.epsilon⁻¹ s
    let K := (cap.carrier ∪ tube.carrier) \ T
    let V := (S.Φ.symm '' cap.closed_core) ∪ S.chartExtension.glued ''
      (univ ×ˢ Ioo (-cap.epsilon⁻¹) s)
    let Sset := S.chartExtension.glued '' (univ ×ˢ ({s} : Set ℝ))
    K ⊆ (cap.carrier ∪ tube.carrier) ∧ IsOpen V ∧ closure V = K ∧
      interior K = V ∧ frontier V = Sset ∧ frontier K = Sset ∧
      frontier (cap.carrier ∪ tube.carrier) ⊆ closure T := by
  dsimp only
  let T0 := cap.end_chart.cylinderTail cap.epsilon⁻¹ s
  let K0 := cap.carrier \ T0
  let V0 := cap.closed_core ∪ cap.end_chart ''
    (univ ×ˢ Ioo (-cap.epsilon⁻¹) s)
  let S0 := cap.end_chart '' (univ ×ˢ ({s} : Set ℝ))
  have hcut := cap.cut_topology s hs
  have hT0sub : T0 ⊆ cap.carrier := by
    dsimp [T0]
    exact cap.end_chart.cylinderTail_subset_target cap.end_chart_source hs.1 |>.trans
      cap.end_chart_target_subset
  have hK0sub : K0 ⊆ cap.carrier := by
    exact sdiff_subset
  have hlow : (univ : Set UnitTwoSphere) ×ˢ Ioo (-cap.epsilon⁻¹) s ⊆
      cap.end_chart.source := by
    rw [cap.end_chart_source]
    exact prod_mono subset_rfl (Ioo_subset_Ioo_right hs.2.le)
  have hslice : (univ : Set UnitTwoSphere) ×ˢ ({s} : Set ℝ) ⊆
      cap.end_chart.source := by
    rw [cap.end_chart_source]
    rintro z ⟨hz, rfl⟩
    exact ⟨mem_univ _, hs⟩
  have hV0sub : V0 ⊆ cap.carrier := by
    dsimp [V0]
    refine union_subset ?_ ?_
    · rw [cap.closed_core_eq_complement_end]
      exact sdiff_subset
    · rintro y ⟨z, hz, rfl⟩
      exact cap.end_chart_target_subset (cap.end_chart.map_source
        (hlow hz))
  have hV0open : IsOpen V0 := by
    simpa only [V0] using hcut.2.1
  have hV0K0 : V0 ⊆ K0 := by
    have hcl := (show closure V0 = K0 by simpa only [V0, K0, T0] using hcut.2.2.1)
    rw [← hcl]
    exact subset_closure
  have hK0compact : IsCompact K0 := by
    simpa only [K0, T0] using cap.compact_tail_complement s hs
  have hS0sub : S0 ⊆ cap.carrier := by
    dsimp [S0]
    rintro y ⟨z, hz, rfl⟩
    exact cap.end_chart_target_subset (cap.end_chart.map_source (hslice hz))
  have hfrontV0 : frontier V0 = S0 := by
    simpa only [V0, S0] using hcut.2.2.2.2.1
  have hfrontK0 : frontier K0 = S0 := by
    simpa only [K0, T0, S0] using hcut.2.2.2.2.2.1
  have hclV : closure V0 = K0 := by
    simpa only [V0, K0, T0] using hcut.2.2.1
  have hinteriorK : interior K0 = V0 := by
    simpa only [V0, K0, T0] using hcut.2.2.2.1
  have hEsource : S.Φ.symm.source = cap.carrier := by
    rw [OpenPartialHomeomorph.symm_source, S.target_eq]
  have image_isImage {A : Set M} (hA : A ⊆ cap.carrier) :
      S.Φ.symm.IsImage A (S.Φ.symm '' A) := by
    apply OpenPartialHomeomorph.IsImage.of_image_eq
    rw [hEsource, inter_eq_right.mpr hA]
    symm
    apply inter_eq_right.mpr
    rintro y ⟨x, hx, rfl⟩
    exact S.Φ.symm.map_source (hEsource.symm ▸ hA hx)
  have hVimg := image_isImage hV0sub
  have hKimg := image_isImage hK0sub
  have hTimg := image_isImage hT0sub
  have himage_diff {A B : Set M} (hA : A ⊆ cap.carrier)
      (hB : B ⊆ cap.carrier) :
      S.Φ.symm '' (A \ B) = (S.Φ.symm '' A) \ S.Φ.symm '' B := by
    apply Subset.antisymm
    · rintro y ⟨x, hx, rfl⟩
      refine ⟨⟨x, hx.1, rfl⟩, ?_⟩
      rintro ⟨z, hz, hzy⟩
      have h := congrArg S.Φ hzy
      rw [S.apply_symm_apply (hB hz), S.apply_symm_apply (hA hx.1)] at h
      exact hx.2 (h ▸ hz)
    · rintro y ⟨⟨x, hx, hxy⟩, hyB⟩
      rcases hyB with hyB
      refine ⟨x, ⟨hx, ?_⟩, hxy⟩
      intro hxB
      apply hyB
      exact ⟨x, hxB, hxy⟩
  have hclosure :
      closure (S.Φ.symm '' V0) = S.Φ.symm '' K0 := by
    apply Subset.antisymm
    · apply closure_minimal (image_mono hV0K0)
      exact hK0compact.image_of_continuousOn
        (S.symm_smooth.continuousOn.mono (hEsource.symm ▸ hK0sub)) |>.isClosed
    · intro y hy
      rcases hy with ⟨x, hx, rfl⟩
      have hy' : S.Φ.symm x ∈ S.Φ.symm.target ∩
          closure (S.Φ.symm '' V0) := by
        rw [← hVimg.closure.image_eq]
        refine ⟨x, ?_, rfl⟩
        exact ⟨by rw [hEsource]; exact hK0sub hx, hclV.symm ▸ hx⟩
      exact hy'.2
  have hinterior :
      interior (S.Φ.symm '' K0) = S.Φ.symm '' V0 := by
    apply Subset.antisymm
    · intro y hy
      have hyK : y ∈ S.Φ.symm '' K0 := interior_subset hy
      have hyT : y ∈ S.Φ.symm.target := by
        rcases hyK with ⟨x, hx, rfl⟩
        exact S.Φ.symm.map_source (hEsource.symm ▸ hK0sub hx)
      have hy' : y ∈ S.Φ.symm.target ∩ interior (S.Φ.symm '' K0) :=
        ⟨hyT, hy⟩
      rw [← hKimg.interior.image_eq] at hy'
      rcases hy' with ⟨x, hx, rfl⟩
      exact ⟨x, hinteriorK.symm ▸ hx.2, rfl⟩
    · have hopen : IsOpen (S.Φ.symm '' V0) :=
        S.Φ.symm.isOpen_image_of_subset_source hV0open
          (hEsource.symm ▸ hV0sub)
      exact interior_maximal (image_mono hV0K0) hopen
  have hTtail :
      S.chartExtension.glued.cylinderTail cap.epsilon⁻¹ s =
        S.Φ.symm '' T0 := by
    simpa only [T0] using S.glued_cylinderTail hs
  have hKeq :
      (cap.carrier ∪ tube.carrier) \
          S.chartExtension.glued.cylinderTail cap.epsilon⁻¹ s =
        S.Φ.symm '' K0 := by
    rw [hTtail, ← S.symm_image_diff hT0sub]
  have hVeq :
      (S.Φ.symm '' cap.closed_core) ∪ S.chartExtension.glued ''
          (univ ×ˢ Ioo (-cap.epsilon⁻¹) s) = S.Φ.symm '' V0 := by
    have hlow' : (univ : Set UnitTwoSphere) ×ˢ Ioo (-cap.epsilon⁻¹) s ⊆
        S.extendedChart.source := by
      rw [S.extendedChart_source]
      exact prod_mono subset_rfl (Ioo_subset_Ioo_right hs.2.le)
    have heq : S.chartExtension.glued ''
          (univ ×ˢ Ioo (-cap.epsilon⁻¹) s) =
        S.extendedChart '' (univ ×ˢ Ioo (-cap.epsilon⁻¹) s) := by
      rw [Set.EqOn.image_eq (Set.EqOn.mono hlow' (S.glued_eq).1)]
    have heq' : S.extendedChart ''
          (univ ×ˢ Ioo (-cap.epsilon⁻¹) s) =
        S.Φ.symm '' (cap.end_chart ''
          (univ ×ˢ Ioo (-cap.epsilon⁻¹) s)) := by
      rw [extendedChart, OpenPartialHomeomorph.coe_trans, image_comp]
    rw [heq, heq']
    rw [← image_union]
  have hSeq :
      S.chartExtension.glued '' (univ ×ˢ ({s} : Set ℝ)) =
        S.Φ.symm '' S0 := by
    have hslice' : (univ : Set UnitTwoSphere) ×ˢ ({s} : Set ℝ) ⊆
        S.extendedChart.source := by
      rw [S.extendedChart_source]
      rintro z ⟨hz, rfl⟩
      exact ⟨mem_univ _, hs⟩
    rw [Set.EqOn.image_eq (Set.EqOn.mono hslice' (S.glued_eq).1),
      ← image_comp]
    rfl
  have hVimgopen : IsOpen (S.Φ.symm '' V0) :=
    S.Φ.symm.isOpen_image_of_subset_source hV0open
      (hEsource.symm ▸ hV0sub)
  have hinteriorV0 : interior V0 = V0 := hV0open.interior_eq
  have hKimgclosed : IsClosed (S.Φ.symm '' K0) :=
    hK0compact.image_of_continuousOn
      (S.symm_smooth.continuousOn.mono (hEsource.symm ▸ hK0sub)) |>.isClosed
  have hKVeq : K0 \ V0 = S0 := by
    calc
      K0 \ V0 = closure V0 \ interior V0 := by rw [hclV, hinteriorV0]
      _ = frontier V0 := rfl
      _ = S0 := hfrontV0
  have hfrontV : frontier (S.Φ.symm '' V0) = S.Φ.symm '' S0 := by
    change closure (S.Φ.symm '' V0) \ interior (S.Φ.symm '' V0) = _
    rw [hclosure, hVimgopen.interior_eq, ← himage_diff hK0sub hV0sub,
      hKVeq]
  have hfrontK : frontier (S.Φ.symm '' K0) = S.Φ.symm '' S0 := by
    change closure (S.Φ.symm '' K0) \ interior (S.Φ.symm '' K0) = _
    rw [hKimgclosed.closure_eq, hinterior, ← himage_diff hK0sub hV0sub,
      hKVeq]
  have hS0closureT0 : S0 ⊆ closure T0 := by
    rw [← hfrontK0]
    intro x hx
    change x ∈ closure K0 \ interior K0 at hx
    have hxC : x ∈ cap.carrier := hS0sub (hfrontK0 ▸ hx)
    apply mem_closure_iff.mpr
    intro O hO hxO
    by_contra hne
    have hsub : O ∩ cap.carrier ⊆ K0 := by
      intro y hy
      refine ⟨hy.2, ?_⟩
      intro hyT
      apply hne
      exact ⟨y, ⟨hy.1, hyT⟩⟩
    have hxint : x ∈ interior K0 :=
      interior_maximal hsub (hO.inter cap.carrier_open) ⟨hxO, hxC⟩
    exact hx.2 hxint
  have hSsetclosure :
      S.chartExtension.glued '' (univ ×ˢ ({s} : Set ℝ)) ⊆
        closure (S.chartExtension.glued.cylinderTail cap.epsilon⁻¹ s) := by
    rw [hSeq, hTtail]
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    have hxsource : x ∈ S.Φ.symm.source := hEsource.symm ▸ hS0sub hx
    exact (hTimg.closure.apply_mem_iff hxsource).2 (hS0closureT0 hx)
  have hfrontVout :
      frontier ((S.Φ.symm '' cap.closed_core) ∪ S.chartExtension.glued ''
        (univ ×ˢ Ioo (-cap.epsilon⁻¹) s)) =
        S.chartExtension.glued '' (univ ×ˢ ({s} : Set ℝ)) := by
    rw [hVeq, hfrontV, hSeq]
  have hfrontKout :
      frontier ((cap.carrier ∪ tube.carrier) \
        S.chartExtension.glued.cylinderTail cap.epsilon⁻¹ s) =
        S.chartExtension.glued '' (univ ×ˢ ({s} : Set ℝ)) := by
    rw [hKeq, hfrontK, hSeq]
  have hfrontU : frontier (cap.carrier ∪ tube.carrier) ⊆
      closure (S.chartExtension.glued.cylinderTail cap.epsilon⁻¹ s) := by
    intro x hx
    by_contra hnot
    change x ∈ closure (cap.carrier ∪ tube.carrier) \
      interior (cap.carrier ∪ tube.carrier) at hx
    have hxK : x ∈ closure ((cap.carrier ∪ tube.carrier) \
        S.chartExtension.glued.cylinderTail cap.epsilon⁻¹ s) := by
      apply mem_closure_iff.mpr
      intro O hO hxO
      have hO' : IsOpen (O ∩
          (closure (S.chartExtension.glued.cylinderTail cap.epsilon⁻¹ s))ᶜ) :=
        hO.inter (isOpen_compl_iff.mpr isClosed_closure)
      have hxO' : x ∈ O ∩
          (closure (S.chartExtension.glued.cylinderTail cap.epsilon⁻¹ s))ᶜ :=
        ⟨hxO, hnot⟩
      obtain ⟨y, hyO, hyU⟩ :=
        (mem_closure_iff.mp hx.1) _ hO' hxO'
      refine ⟨y, hyO.1, ⟨hyU, ?_⟩⟩
      intro hyT
      exact hyO.2 (subset_closure hyT)
    have hxnotint : x ∉ interior ((cap.carrier ∪ tube.carrier) \
        S.chartExtension.glued.cylinderTail cap.epsilon⁻¹ s) := by
      intro hxint
      exact hx.2 (interior_mono sdiff_subset hxint)
    have hxS := hfrontKout ▸ (show x ∈ frontier ((cap.carrier ∪ tube.carrier) \
        S.chartExtension.glued.cylinderTail cap.epsilon⁻¹ s) from
        ⟨hxK, hxnotint⟩)
    exact hnot (hSsetclosure hxS)
  refine ⟨sdiff_subset, ?_, ?_, ?_, hfrontVout, hfrontKout, hfrontU⟩
  · rw [hVeq]
    exact hVimgopen
  · rw [hVeq, hclosure, hKeq]
  · rw [hKeq, hinterior, hVeq]
noncomputable def modelEquivalence :
    CapModelEquivalence cap.model_kind cap.puncture
      (cap.carrier ∪ tube.carrier) where
  model := cap.model_equivalence.model
  model_topology := cap.model_equivalence.model_topology
  model_charted := cap.model_equivalence.model_charted
  model_manifold := cap.model_equivalence.model_manifold
  standard_model := cap.model_equivalence.standard_model
  standard_smooth := cap.model_equivalence.standard_smooth
  forward := fun x => cap.model_equivalence.forward (S.Φ x)
  inverse := fun y => S.Φ.symm (cap.model_equivalence.inverse y)
  inverse_mem := fun y => S.symm_mem (cap.model_equivalence.inverse_mem y)
  left_inverse := by
    intro x hx
    show S.Φ.symm (cap.model_equivalence.inverse (cap.model_equivalence.forward (S.Φ x))) = x
    rw [cap.model_equivalence.left_inverse _ (S.map_mem hx), S.symm_apply_apply hx]
  right_inverse := by
    intro y
    show cap.model_equivalence.forward
      (S.Φ (S.Φ.symm (cap.model_equivalence.inverse y))) = y
    rw [S.apply_symm_apply (cap.model_equivalence.inverse_mem y),
      cap.model_equivalence.right_inverse]
  forward_smooth := by
    let _i₁ := cap.model_equivalence.model_topology
    let _i₂ := cap.model_equivalence.model_charted
    let _i₃ := cap.model_equivalence.model_manifold
    exact cap.model_equivalence.forward_smooth.comp S.smooth
      (fun x hx => S.map_mem hx)
  inverse_smooth := by
    let _i₁ := cap.model_equivalence.model_topology
    let _i₂ := cap.model_equivalence.model_charted
    let _i₃ := cap.model_equivalence.model_manifold
    exact S.symm_smooth.comp cap.model_equivalence.inverse_smooth
      (fun y _ => cap.model_equivalence.inverse_mem y)
noncomputable def absorptionData
    (hconn : IsConnected (cap.carrier ∪ tube.carrier)) :
    CapTubeAbsorptionData cap tube where
  chart := S.chartExtension
  carrier_open := cap.carrier_open.union tube.carrier_open
  puncture := cap.puncture
  puncture_eq := rfl
  model_equivalence := S.modelEquivalence
  closed_core := S.Φ.symm '' cap.closed_core
  closed_core_compact :=
    cap.closed_core_compact.image_of_continuousOn
      (S.symm_smooth.continuousOn.mono (by
        rw [cap.closed_core_eq_complement_end]
        exact sdiff_subset))
  closed_core_eq_complement_end := by
    rw [(S.glued_eq).2, S.extendedChart_target,
      cap.closed_core_eq_complement_end,
      S.symm_image_diff cap.end_chart_target_subset]
  compact_tail_complement := by
    intro s hs
    have hsub : cap.end_chart.cylinderTail cap.epsilon⁻¹ s ⊆ cap.carrier :=
      (cap.end_chart.cylinderTail_subset_target cap.end_chart_source hs.1).trans
        cap.end_chart_target_subset
    rw [S.glued_cylinderTail hs, ← S.symm_image_diff hsub]
    exact (cap.compact_tail_complement s hs).image_of_continuousOn
      (S.symm_smooth.continuousOn.mono sdiff_subset)
  cut_topology := S.cut_topology_transport
  core := S.Φ.symm '' cap.core
  core_nonempty := cap.core_nonempty.image _
  core_subset_closed_core := image_mono cap.core_subset_closed_core
  carrier_connected := hconn
end CollarShrinkData
theorem exists_capTubeAbsorptionData
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
    [T3Space M] {g : RiemannianMetric 3 M} {X : Set M}
    (cap : ClosedModelCapData g) (tube : EpsilonTubeCertificate g X) (side : Bool)
    (_A : ClosedModelCapTubeAttachment cap tube side)
    (S : CollarShrinkData cap tube side) :
    Nonempty (CapTubeAbsorptionData cap tube) := by
  have hconn : IsConnected (cap.carrier ∪ tube.carrier) := by
    rw [← S.symm_image_carrier]
    exact cap.carrier_connected.image _ S.symm_smooth.continuousOn
  exact ⟨S.absorptionData hconn⟩
end PoincareConjecture.M25.Topology3D
