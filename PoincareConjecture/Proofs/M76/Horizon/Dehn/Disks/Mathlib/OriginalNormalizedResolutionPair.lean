import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Mathlib.NormalizedResolutionPair
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Mathlib.OriginalStripResolutionMaps
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Mathlib.MarkedIntervalDiskAttachment
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Mathlib.ResolutionStripBoundary
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.PolygonalStripDiskAttachment
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Loops.Mathlib.OriginalResolutionPairAlignment

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76.Dehn.PolygonalCrossingResolution

local notation "P2" => (ℝ × ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "Q2" => sphere (0 : V2) 1
local notation "D2" => closedBall (0 : V2) 1
local notation "I01" => Icc (0 : ℝ) 1

structure OriginalNormalizedResolutionPairData
    {F X ι : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace X]
    (e : ι → OpenPartialHomeomorph X F)
    {f : V2 → X} {Z : Set X} {base : Z} {G : Subgroup (FundamentalGroup Z base)}
    {c : Bool → P2 → V2} {τ : C3 → X}
    (D : OriginalResolutionWordExclusionData f Z base G c τ (1 / 4)) where
  gU : V2 → X
  gV : V2 → X
  sourceU : UpperResolutionSources D.A D.C source
    (fun t ↦ c false ((t : ℝ), farArmParameter (!D.s0)))
    (fun t ↦ c true ((t : ℝ), farArmParameter (!D.s1)))
    (fun t ↦ ⟨((t : ℝ), -1), t.property, by norm_num⟩)
    (fun t ↦ ⟨((t : ℝ), 1), t.property, by norm_num⟩)
    f ((τ ∘ tubeArmOrientation D.s0 D.s1) ∘ strip (1 / 4) true) f gU
  sourceV : AlternateResolutionSources D.A D.M D.C source
    (fun t ↦ c false ((t : ℝ), farArmParameter (!D.s0)))
    (fun t ↦ c true ((t : ℝ), farArmParameter D.s1))
    (fun t ↦ c false ((t : ℝ), farArmParameter D.s0))
    (fun t ↦ c true ((t : ℝ), farArmParameter (!D.s1)))
    (fun t ↦ ⟨((t : ℝ), -1), t.property, by norm_num⟩)
    (fun t ↦ ⟨((t : ℝ), 1), t.property, by norm_num⟩)
    f ((τ ∘ tubeArmOrientation D.s0 D.s1) ∘ alternate (1 / 4) false)
    f ((τ ∘ tubeArmOrientation D.s0 D.s1) ∘ alternate (1 / 4) true) f gV
  plU : PolyhedralPLInCharts e gU D2
  plV : PolyhedralPLInCharts e gV D2
  imageU : gU '' D2 = (f '' D.A ∪ (τ ∘ tubeArmOrientation D.s0 D.s1) ''
    (strip (1 / 4) true '' source)) ∪ f '' D.C
  imageV : gV '' D2 = (((f '' D.A ∪ (τ ∘ tubeArmOrientation D.s0 D.s1) ''
    (alternate (1 / 4) false '' source)) ∪ f '' D.M) ∪
    (τ ∘ tubeArmOrientation D.s0 D.s1) '' (alternate (1 / 4) true '' source)) ∪ f '' D.C
  properU : ∀ x ∈ D2, gU x ∈ Z ↔ x ∈ Q2
  properV : ∀ x ∈ D2, gV x ∈ Z ↔ x ∈ Q2
  RU : Path D.E0.c D.E0.c
  RV : Path D.E0.c D.E0.c
  rimU : ∀ t : I01, (RU t : X) = gU (squareRimLoop t)
  rimV : ∀ t : I01, (RV t : X) = gV (squareRimLoop t)
  whisker : Path base D.E0.c
  outside : whisker.whiskeredLoopClass RU ∉ G ∨ whisker.whiskeredLoopClass RV ∉ G

theorem nonempty_original_normalized_resolution_pair_data
    {F X ι : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [TopologicalSpace X] (e : ι → OpenPartialHomeomorph X F)
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid F)
    {f : V2 → X} {Z : Set X} {base : Z} {G : Subgroup (FundamentalGroup Z base)} [G.Normal]
    {c : Bool → P2 → V2} {τ : C3 → X}
    (D : OriginalResolutionWordExclusionData f Z base G c τ (1 / 4))
    (hcPL : ∀ i, FinitePiecewiseAffineOn (c i) source)
    (hci : ∀ i, InjOn (c i) source) (hcS : ∀ i, MapsTo (c i) source D2)
    (hcQ : ∀ i x, x ∈ source → (c i x ∈ Q2 ↔ x.1 = 0 ∨ x.1 = 1))
    (hdisj : Disjoint (c false '' source) (c true '' source))
    (hf : PolyhedralPLInCharts e f D2) (hτ : PolyhedralPLInCharts e τ tube)
    (h0 : ∀ p ∈ source, f (c false p) = τ ((p.2, p.2), p.1))
    (h1 : ∀ p ∈ source, f (c true p) = τ ((p.2, -p.2), p.1))
    (hfZ : ∀ x ∈ D2, f x ∈ Z ↔ x ∈ Q2)
    (hτZ : ∀ z ∈ tube, τ z ∈ Z ↔ z.2 = 0 ∨ z.2 = 1)
    (rim : C(Q2, Z)) (hboundary : ∀ x : Q2, f x = (rim x : X))
    (basepath : Path base (rim squareRimBase)) :
    Nonempty (OriginalNormalizedResolutionPairData e D) := by
  have hAS : D.A ⊆ D2 := fun x hx ↦ D.cover.subset (Or.inl (Or.inl (Or.inl hx)))
  have hMS : D.M ⊆ D2 := fun x hx ↦ D.cover.subset (Or.inl (Or.inl (Or.inr hx)))
  have hCS : D.C ⊆ D2 := fun x hx ↦ D.cover.subset (Or.inl (Or.inr hx))
  have hfA := polyhedralPL_restrict_disk hf D.diskA hAS
  have hfM := polyhedralPL_restrict_disk hf D.diskM hMS
  have hfC := polyhedralPL_restrict_disk hf D.diskC hCS
  have hfar (s : Bool) : farArmParameter s ∈ Icc (-1 : ℝ) 1 := by
    cases s <;> norm_num [farArmParameter]
  obtain ⟨hWA, habA, pA, hpA, hpAval⟩ :=
    exists_embedded_strip_arm_parameter (c false) (hcPL false) (hci false)
      (farArmParameter (!D.s0)) (hfar (!D.s0))
  obtain ⟨hLM, habL, pL, hpL, hpLval⟩ :=
    exists_embedded_strip_arm_parameter (c true) (hcPL true) (hci true)
      (farArmParameter D.s1) (hfar D.s1)
  obtain ⟨hRM, _, pR, hpR, hpRval⟩ :=
    exists_embedded_strip_arm_parameter (c false) (hcPL false) (hci false)
      (farArmParameter D.s0) (hfar D.s0)
  obtain ⟨hWC, habC, pC, hpC, hpCval⟩ :=
    exists_embedded_strip_arm_parameter (c true) (hcPL true) (hci true)
      (farArmParameter (!D.s1)) (hfar (!D.s1))
  have hLMRM := hdisj.symm.mono (image_mono (arm_far_subset_source D.s1))
    (image_mono (arm_far_subset_source D.s0))
  let τ' := τ ∘ tubeArmOrientation D.s0 D.s1
  have hτ' : PolyhedralPLInCharts e τ' tube := reoriented_tube_polyhedralPL e hτ D.s0 D.s1
  have hτ'Z := reoriented_tube_frontier_iff τ hτZ D.s0 D.s1
  have hcorners := reoriented_tube_old_arm_equations f (c false) (c true) τ h0 h1 D.s0 D.s1
  have hAeq (t : I01) : f (pA t) = τ' ((-1, 1), t) := by
    rw [hpAval]
    exact (hcorners t).1
  have hLeq (t : I01) : f (pL t) = τ' ((-1, -1), t) := by
    rw [hpLval]
    exact (hcorners t).2.1
  have hReq (t : I01) : f (pR t) = τ' ((1, -1), t) := by
    rw [hpRval]
    exact (hcorners t).2.2.1
  have hCeq (t : I01) : f (pC t) = τ' ((1, 1), t) := by
    rw [hpCval]
    exact (hcorners t).2.2.2
  have hAQ := retained_piece_frontier_preimage f hfZ hAS
  have hMQ := retained_piece_frontier_preimage f hfZ hMS
  have hCQ := retained_piece_frontier_preimage f hfZ hCS
  have hmark (i s : Bool) := original_strip_arm_frontier_inter f (c i) hfZ
    (hcS i) (hcQ i) (farArmParameter s) (hfar s)
  have hpair := exists_normalized_resolution_pair e hcompat D.diskA D.diskM D.diskC
    hWA hLM hRM hWC subset_union_right subset_union_right
    (subset_union_right.trans subset_union_left) subset_union_right hLMRM habA habL habC
    pA pL pR pC hpA hpL hpR hpC (hpAval 0) (hpAval 1) (hpLval 0) (hpLval 1)
    (hpRval 0) (hpRval 1) (hpCval 0) (hpCval 1) hfA hfM hfC hτ' hAeq hLeq hReq hCeq
    Z hτ'Z (by rw [hAQ]) (by rw [hMQ]) (by rw [hCQ])
    (hmark false (!D.s0)) (hmark true D.s1) (hmark false D.s0) (hmark true (!D.s1))
  simp only [hMQ] at hpair
  obtain ⟨d0, d1, J, K, qA, qC, qD, qB, a, γ, gU, gV, RU, RV, sourcesU, sourcesV,
    _, _, _, _, hqA0, hqA1, hqC0, hqC1, hqD0, hqB1, _, hJK,
    haval, hcval, hgU, hgV, himU, himV, hproperU, hproperV, hRU, hRV, hRUhom, hcases⟩ := hpair
  have hd0 : d0 = D.E0 := d0.eq D.E0
  have hd1 : d1 = D.E1 := d1.eq D.E1
  subst d0 d1
  obtain ⟨p, q⟩ := D.nonempty_center_paths rim hboundary basepath
  let qA' := qA.trans (Homeomorph.setCongr hAQ)
  let qC' := qC.trans (Homeomorph.setCongr hCQ)
  have hmarkQ : MapsTo f Q2 Z := fun x hx ↦ (hfZ x (sphere_subset_closedBall hx)).mpr hx
  have hout := original_resolution_pair_excluded D hf.continuousOn hmarkQ
    qA' qC' qD qB hqA0 hqA1 hqC0 hqC1 hqD0 hqB1 hJK a γ haval hcval
    RU RV hRUhom hcases p q
  have hpAfun : (fun t : I01 ↦ (pA t : V2)) =
      (fun t : I01 ↦ c false ((t : ℝ), farArmParameter (!D.s0))) := funext hpAval
  have hpLfun : (fun t : I01 ↦ (pL t : V2)) =
      (fun t : I01 ↦ c true ((t : ℝ), farArmParameter D.s1)) := funext hpLval
  have hpRfun : (fun t : I01 ↦ (pR t : V2)) =
      (fun t : I01 ↦ c false ((t : ℝ), farArmParameter D.s0)) := funext hpRval
  have hpCfun : (fun t : I01 ↦ (pC t : V2)) =
      (fun t : I01 ↦ c true ((t : ℝ), farArmParameter (!D.s1))) := funext hpCval
  rw [hpAfun, hpCfun] at sourcesU
  rw [hpAfun, hpLfun, hpRfun, hpCfun] at sourcesV
  exact ⟨{
    gU := gU, gV := gV, sourceU := sourcesU.some, sourceV := sourcesV.some
    plU := hgU, plV := hgV, imageU := himU, imageV := himV
    properU := hproperU, properV := hproperV, RU := RU, RV := RV, rimU := hRU, rimV := hRV
    whisker := p.trans D.E0.rc, outside := hout }⟩

theorem OriginalNormalizedResolutionPairData.exists_selected
    {F X ι : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X F}
    {f : V2 → X} {Z : Set X} {base : Z} {G : Subgroup (FundamentalGroup Z base)}
    {c : Bool → P2 → V2} {τ : C3 → X}
    {D : OriginalResolutionWordExclusionData f Z base G c τ (1 / 4)}
    (P : OriginalNormalizedResolutionPairData e D) :
    ∃ (g : V2 → X) (rho : Path D.E0.c D.E0.c),
      PolyhedralPLInCharts e g D2 ∧ (∀ x ∈ D2, g x ∈ Z ↔ x ∈ Q2) ∧
      (∀ t : I01, (rho t : X) = g (squareRimLoop t)) ∧
      P.whisker.whiskeredLoopClass rho ∉ G ∧
      ((g = P.gU ∧ rho = P.RU) ∨ (g = P.gV ∧ rho = P.RV)) := by
  rcases P.outside with hU | hV
  · exact ⟨P.gU, P.RU, P.plU, P.properU, P.rimU, hU, Or.inl ⟨rfl, rfl⟩⟩
  · exact ⟨P.gV, P.RV, P.plV, P.properV, P.rimV, hV, Or.inr ⟨rfl, rfl⟩⟩

theorem exists_original_selected_normalized_resolution
    {F X ι : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [TopologicalSpace X] (e : ι → OpenPartialHomeomorph X F)
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid F)
    {f : V2 → X} {Z : Set X} {base : Z} {G : Subgroup (FundamentalGroup Z base)} [G.Normal]
    (hf : PolyhedralPLInCharts e f D2)
    (rim : C(Q2, Z)) (hboundary : ∀ x : Q2, f x = (rim x : X))
    (basepath : Path base (rim squareRimBase))
    (houtside : basepath.whiskeredLoopClass (squareRimLoop.map rim.continuous) ∉ G)
    (c : Bool → P2 → V2)
    (hcPL : ∀ i, FinitePiecewiseAffineOn (c i) source)
    (hci : ∀ i, InjOn (c i) source) (hcS : ∀ i, MapsTo (c i) source D2)
    (hcQ : ∀ i x, x ∈ source → (c i x ∈ Q2 ↔ x.1 = 0 ∨ x.1 = 1))
    (hdisj : Disjoint (c false '' source) (c true '' source))
    {τ : C3 → X} (hτ : PolyhedralPLInCharts e τ tube)
    (h0 : ∀ p ∈ source, f (c false p) = τ ((p.2, p.2), p.1))
    (h1 : ∀ p ∈ source, f (c true p) = τ ((p.2, -p.2), p.1))
    (hfZ : ∀ x ∈ D2, f x ∈ Z ↔ x ∈ Q2)
    (hτZ : ∀ z ∈ tube, τ z ∈ Z ↔ z.2 = 0 ∨ z.2 = 1) :
    ∃ (D : OriginalResolutionWordExclusionData f Z base G c τ (1 / 4))
      (P : OriginalNormalizedResolutionPairData e D) (g : V2 → X)
      (rho : Path D.E0.c D.E0.c),
      PolyhedralPLInCharts e g D2 ∧ (∀ x ∈ D2, g x ∈ Z ↔ x ∈ Q2) ∧
      (∀ t : I01, (rho t : X) = g (squareRimLoop t)) ∧
      P.whisker.whiskeredLoopClass rho ∉ G ∧
      ((g = P.gU ∧ rho = P.RU) ∨ (g = P.gV ∧ rho = P.RV)) := by
  obtain ⟨D⟩ := nonempty_original_resolution_word_exclusion_data f hf.continuousOn
    rim hboundary basepath houtside c hcPL hci hcS hcQ hdisj τ hτ.continuousOn
    (fun z hz ht ↦ (hτZ z hz).mpr ht) h0 h1 (by norm_num : (1 / 4 : ℝ) < 1)
  obtain ⟨P⟩ := nonempty_original_normalized_resolution_pair_data e hcompat D
    hcPL hci hcS hcQ hdisj hf hτ h0 h1 hfZ hτZ rim hboundary basepath
  obtain ⟨g, rho, hg, hproper, hrim, hout, hchoice⟩ := P.exists_selected
  exact ⟨D, P, g, rho, hg, hproper, hrim, hout, hchoice⟩

end PoincareConjecture.M76.Dehn.PolygonalCrossingResolution
