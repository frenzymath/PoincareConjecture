import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Disks.RimBands.Collar.Orientation.Collars.DiskNormalLabel
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Disks.RimBands.Collar.Orientation.Collars.CanonicalTubeNormal
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Disks.RimBands.Collar.Orientation.Collars.NormalLabelComparison
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Disks.RimBands.Collar.Orientation.Collars.TubeNormalChart
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Disks.RimBands.Coordinates.ArmIncidence








set_option autoImplicit false

open Set Metric Geometry Topology Filter

namespace PoincareConjecture.M76.Dehn.Annuli.RimBands

open TubeExterior TubeExterior.CornerBands PolygonalCrossingResolution

local notation "P2" => (ℝ × ℝ)
local notation "C3" => (P2 × ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Disk" => closedBall (0 : V2) 1
local notation "I" => Icc (0 : ℝ) 1

private noncomputable def armMidpointCoordinates
    (r w : ℝ) (side b o : Bool) (s : ℝ) : C3 :=
  bandMap r (b, if side then !b else b)
    (armCoordinates w 0 1 b (sign o * s, 1 / 2))

private theorem continuous_armMidpointCoordinates (r w : ℝ) (side b o : Bool) :
    Continuous (armMidpointCoordinates r w side b o) := by
  unfold armMidpointCoordinates
  simp only [armCoordinates_apply, bandMap, arcMap]
  fun_prop

private theorem armMidpointCoordinates_zero (r w : ℝ) (side b o : Bool) :
    armMidpointCoordinates r w side b o 0 =
      ((sign b * r, sign (if side then !b else b) * r), 1 / 2) := by
  simp [armMidpointCoordinates, armCoordinates_apply, bandMap, arcMap]

private theorem signed_radius_mem {r : ℝ} (hr : 0 < r) (hr1 : r < 1) (b : Bool) :
    sign b * r ∈ Ioo (-1 : ℝ) 1 := by
  cases b <;> simp only [sign, Bool.false_eq_true, if_false, if_true, one_mul, neg_one_mul]
  all_goals constructor <;> linarith

private theorem armMidpointCoordinates_zero_interior
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1) (w : ℝ) (side b o : Bool) :
    armMidpointCoordinates r w side b o 0 ∈ interior tube := by
  rw [armMidpointCoordinates_zero]
  simp only [tube, interior_prod_eq, interior_Icc]
  exact ⟨⟨signed_radius_mem hr hr1 b, signed_radius_mem hr hr1 _⟩, by norm_num⟩



theorem orientation_eq_of_actual_signed_arms
    {X ι κ : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {R W Q : Set X}
    {S T C D : Set P2} {f₀ f₁ : P2 → X} {j : V2 → X}
    (U : OriginalIntervalTube e R W S T C D f₀ f₁) (side : Bool)
    {r w : ℝ} (hr : 0 < r) (hr1 : r < 1) (hw : 0 < w)
    (P : OriginalDiskProduct e Q j) (hQ : IsClosed Q) (hQR : Q ⊆ R)
    (himage : j '' Disk = (if side then f₁ '' T else f₀ '' S) ∩ Q)
    (o : Bool → Bool)
    (harms : ∀ b t, t ∈ I → ∀ s ∈ Icc (-1 : ℝ) 1,
      P.map (rimArm b t, s) = prescribedArmBand U r w 0 1 side b (sign (o b) * s, t))
    (E : κ → OpenPartialHomeomorph X C3)
    (hcover : ∀ x ∈ (if side then f₁ '' T else f₀ '' S) \ frontier R,
      ∃ i, x ∈ (E i).source)
    (hpair : ∀ i y, y ∈ (E i).source →
      (y ∈ (if side then f₁ '' T else f₀ '' S) \ frontier R ↔ (E i y).2 = 0))
    (hcompat : ∀ i k (x : ((if side then f₁ '' T else f₀ '' S) \ frontier R : Set X)),
      (x : X) ∈ (E i).source ∩ (E k).source →
        ∃ V : Set X, IsOpen V ∧ (x : X) ∈ V ∧
          EqOn (fun y => SignType.sign (E i y).2) (fun y => SignType.sign (E k y).2) V) :
    o false = o true := by
  let B := Disk ∩ j ⁻¹' (frontier R)ᶜ
  let F := fun z : B × ℝ => P.map (z.1, z.2)
  let G := canonicalTubeCollar U side
  obtain ⟨ν, _, hν⟩ := exists_constant_disk_normal_label_off_original_frontier
    P hQ hQR himage E hcover hpair hcompat
  obtain ⟨μ, hμ, hgμ⟩ := exists_constant_canonicalTube_normal_label
    U side E hcover hpair hcompat
  obtain ⟨K, hKs, _, hKv, hKdis, hKpair⟩ :=
    exists_original_tube_normal_chart_off_frontier U side
  have hhalf : (1 / 2 : ℝ) ∈ I := by norm_num
  have hrim (b : Bool) : rimArm b (1 / 2) ∈ Disk :=
    sphere_subset_closedBall (rimArm_mem hhalf)
  have hphysical (b : Bool) (s : ℝ) (hs : s ∈ Icc (-1 : ℝ) 1) :
      P.map (rimArm b (1 / 2), s) = U.map (armMidpointCoordinates r w side b (o b) s) :=
    harms b (1 / 2) hhalf s hs
  have hcenter (b : Bool) :
      j (rimArm b (1 / 2)) = U.map (armMidpointCoordinates r w side b (o b) 0) :=
    (P.central _ (hrim b)).symm.trans (hphysical b 0 (by norm_num))
  have hpB (b : Bool) : rimArm b (1 / 2) ∈ B := by
    refine ⟨hrim b, ?_⟩
    intro hfront
    exact disjoint_left.mp (original_tube_interior_disjoint_frontier U)
      ⟨_, armMidpointCoordinates_zero_interior hr hr1 w side b (o b), (hcenter b).symm⟩ hfront
  let p (b : Bool) : B := ⟨rimArm b (1 / 2), hpB b⟩
  let q (b : Bool) : canonicalTubeBase :=
    ⟨(sign b * r, 1 / 2), signed_radius_mem hr hr1 b, by norm_num⟩
  have hcanonical (b : Bool) :
      canonicalTubeCoordinates side ((q b).val, 0) =
        armMidpointCoordinates r w side b (o b) 0 := by
    rw [armMidpointCoordinates_zero]
    cases side <;> cases b <;> simp [canonicalTubeCoordinates, q, sign]
  have hF : ContinuousOn F (univ ×ˢ Ioo (-1 : ℝ) 1) :=
    P.polyhedral.continuousOn.comp
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd).continuousOn
      (fun z hz => ⟨z.1.property.1, hz.2.1.le, hz.2.2.le⟩)
  have hcompare (b : Bool) : ν = SignType.sign (w * sign (o b)) * μ := by
    have hF0 : F (p b, 0) = U.map (armMidpointCoordinates r w side b (o b) 0) :=
      hphysical b 0 (by norm_num)
    have hbase : F (p b, 0) = G (q b, 0) := by
      rw [hF0]
      change _ = U.map (canonicalTubeCoordinates side ((q b).val, 0))
      rw [hcanonical b]
    have hS : F (p b, 0) ∈ (if side then f₁ '' T else f₀ '' S) \ frontier R := by
      change P.map (rimArm b (1 / 2), 0) ∈ _
      rw [P.central _ (hrim b)]
      exact ⟨(himage.subset (mem_image_of_mem j (hrim b))).1, (hpB b).2⟩
    have hK : F (p b, 0) ∈ K.source := by
      rw [hKs, hF0]
      exact mem_image_of_mem _ (armMidpointCoordinates_zero_interior hr hr1 w side b (o b))
    have hFe : ∀ᶠ s in 𝓝 (0 : ℝ),
        armMidpointCoordinates r w side b (o b) s ∈ interior tube :=
      (continuous_armMidpointCoordinates r w side b (o b)).continuousAt.preimage_mem_nhds
        (isOpen_interior.mem_nhds (armMidpointCoordinates_zero_interior hr hr1 w side b (o b)))
    have hheightF : ∀ᶠ s in 𝓝 (0 : ℝ), (K (F (p b, s))).2 = (w * sign (o b)) * s := by
      filter_upwards [hFe, Ioo_mem_nhds (by norm_num : (-1 : ℝ) < 0)
        (by norm_num : (0 : ℝ) < 1)] with s hs hsmall
      change (K (P.map (rimArm b (1 / 2), s))).2 = _
      rw [hphysical b s ⟨hsmall.1.le, hsmall.2.le⟩, hKv _ hs]
      change tubeNormal side (armMidpointCoordinates r w side b (o b) s) = _
      rw [armMidpointCoordinates, tubeNormal_signed_armCoordinates]
      ring
    have hGe : ∀ᶠ s in 𝓝 (0 : ℝ), (q b, s) ∈ canonicalTubeDomain side :=
      (continuous_const.prodMk continuous_id).continuousAt.preimage_mem_nhds
        ((isOpen_canonicalTubeDomain side).mem_nhds (canonicalTubeDomain_zero side (q b)))
    have hheightG : ∀ᶠ s in 𝓝 (0 : ℝ), (K (G (q b, s))).2 = s := by
      filter_upwards [hGe] with s hs
      change (K (U.map (canonicalTubeCoordinates side ((q b).val, s)))).2 = s
      rw [hKv _ hs]
      exact tubeNormal_canonicalTubeCoordinates side _
    exact positive_normal_labels_eq_of_tube_coordinates E hpair hcompat K
      (fun y hy => (hKpair y hy).symm) F G (p b) (q b)
      (hF.continuousAt ((isOpen_univ.prod isOpen_Ioo).mem_nhds ⟨mem_univ _, by norm_num⟩))
      ((continuousOn_canonicalTubeCollar U side).continuousAt
        ((isOpen_canonicalTubeDomain side).mem_nhds (canonicalTubeDomain_zero side (q b))))
      hbase hS hK ν μ (hν (p b)) (hgμ (q b)) (w * sign (o b)) hheightF hheightG
  have heq := mul_right_cancel₀ hμ ((hcompare false).symm.trans (hcompare true))
  rw [sign_mul, sign_mul, sign_pos hw, one_mul, one_mul] at heq
  cases h0 : o false <;> cases h1 : o true <;> simp_all [sign]

end PoincareConjecture.M76.Dehn.Annuli.RimBands
