import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Protection.OriginalProtectedBallProduct
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Boundary.Push.ProductSide







set_option autoImplicit false
noncomputable section
open Set Metric Geometry Topology

namespace PoincareConjecture.M76
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "P3" => ((ℝ × ℝ) × ℝ)
local notation "Disk" => closedBall (0 : V2) 1
local notation "Rim" => sphere (0 : V2) 1
local notation "I" => Icc (-1 : ℝ) 1
local notation "Unit" => Icc (0 : ℝ) 1
local notation "Cube" => ((I ×ˢ I) ×ˢ I : Set P3)

def protectedEndpointMap {X : Type*} (p : P3 → X) (side : Bool) (z : V2) : X :=
  p ((z 0, z 1), if side then 1 else -1)

private theorem disk_pair_coordinates {z : V2} (hz : z ∈ Disk) :
    (z 0, z 1) ∈ (I ×ˢ I : Set (ℝ × ℝ)) := by
  have hb (i : Fin 2) : |z i| ≤ 1 :=
    (norm_le_pi_norm z i).trans (mem_closedBall_zero_iff.mp hz)
  exact ⟨abs_le.mp (hb 0), abs_le.mp (hb 1)⟩

private theorem disk_rim_coordinates {z : V2} (hz : z ∈ Disk) :
    z ∈ Rim ↔ |z 0| = 1 ∨ |z 1| = 1 := by
  have hn := mem_closedBall_zero_iff.mp hz
  rw [mem_sphere_zero_iff_norm]
  constructor
  · intro h
    by_contra! he
    have hlt : ‖z‖ < 1 := (pi_norm_lt_iff zero_lt_one).mpr (by
      rw [Fin.forall_fin_two]
      constructor
      · exact lt_of_le_of_ne ((norm_le_pi_norm z 0).trans hn)
          (by simpa only [Real.norm_eq_abs] using he.1)
      · exact lt_of_le_of_ne ((norm_le_pi_norm z 1).trans hn)
          (by simpa only [Real.norm_eq_abs] using he.2))
    linarith
  · rintro (h | h)
    · exact le_antisymm hn (by simpa only [Real.norm_eq_abs, h] using norm_le_pi_norm z 0)
    · exact le_antisymm hn (by simpa only [Real.norm_eq_abs, h] using norm_le_pi_norm z 1)

theorem protectedEndpointMap_image {X : Type*} (p : P3 → X) (side : Bool) :
    protectedEndpointMap p side '' Disk = p '' ((I ×ˢ I) ×ˢ {if side then (1 : ℝ) else -1}) := by
  apply Subset.antisymm
  · rintro x ⟨z, hz, rfl⟩
    exact ⟨((z 0, z 1), if side then 1 else -1), ⟨disk_pair_coordinates hz, rfl⟩, rfl⟩
  · rintro x ⟨z, ⟨hz, ht⟩, rfl⟩
    let w : V2 := ![z.1.1, z.1.2]
    have hw : w ∈ Disk := by
      rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
      intro i
      fin_cases i
      · exact abs_le.mpr hz.1
      · exact abs_le.mpr hz.2
    refine ⟨w, hw, ?_⟩
    apply congrArg p
    exact Prod.ext rfl ht.symm

theorem exists_outward_product_at_protected_endpoint
    {X α : Type*} [TopologicalSpace X] [T2Space X]
    {e : α → OpenPartialHomeomorph X V3} {R D O : Set X}
    (hR : IsCompact R) (he : PLDomain e R) (hDR : D ⊆ R)
    (p : P3 → X) (hp : PolyhedralPLInCharts e p Cube) (hpi : InjOn p Cube)
    (hpimage : p '' Cube = D)
    (hproper : ∀ z ∈ Cube, p z ∈ frontier R ↔ |z.1.1| = 1 ∨ |z.1.2| = 1)
    (side : Bool) (hO : IsOpen O) (hendO : protectedEndpointMap p side '' Disk ⊆ O) :
    ∃ (P : OriginalDiskProduct e R (protectedEndpointMap p side))
      (δ : ℝ) (positive : Bool),
      MapsTo P.map (Disk ×ˢ I) O ∧ 0 < δ ∧ δ ≤ 1 / 2 ∧
      ∀ (q : Disk) (t : I),
        (if positive then (t : ℝ) ∈ Ico (-δ) 0 else (t : ℝ) ∈ Ioc 0 δ) →
          P.map ((q : V2), (t : ℝ)) ∉ D := by
  classical
  let sign : ℝ := if side then 1 else -1
  have hsign : sign = 1 ∨ sign = -1 := by cases side <;> simp [sign]
  let a : V2 →ᴬ[ℝ] P3 :=
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0).prod
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 1)).toContinuousAffineMap.prod
        (ContinuousAffineMap.const ℝ V2 sign)
  have haCube : MapsTo a Disk Cube := by
    intro z hz
    exact ⟨disk_pair_coordinates hz, by rcases hsign with h | h <;> simp [a, h]⟩
  have haj : ∀ z, p (a z) = protectedEndpointMap p side z := fun _ => rfl
  have hjPL : PolyhedralPLInCharts e (protectedEndpointMap p side) Disk := by
    obtain ⟨K, _, hK, hKs, _, _⟩ :=
      (isFinitePLBallPair_unit_cube (ι := Fin 2)).exists_finite_carrier_and_rim_complexes
    rw [← hKs]
    exact hp.comp_finitePiecewiseAffineOn K hK
      ((K.affineOnFaces_affine a).finitePiecewiseAffineOn hK)
      (fun z hz => haCube (hKs.subset hz))
  have hji : InjOn (protectedEndpointMap p side) Disk := by
    intro z hz w hw h
    have hh := hpi (haCube hz) (haCube hw) h
    have h0 := congrArg (fun x : P3 => x.1.1) hh
    have h1 := congrArg (fun x : P3 => x.1.2) hh
    ext i
    fin_cases i
    · exact h0
    · exact h1
  have hjR : MapsTo (protectedEndpointMap p side) Disk R :=
    fun z hz => hDR (hpimage.subset ⟨a z, haCube hz, rfl⟩)
  have hjproper (z : V2) (hz : z ∈ Disk) : protectedEndpointMap p side z ∈ frontier R ↔ z ∈ Rim :=
    (hproper (a z) (haCube hz)).trans (disk_rim_coordinates hz).symm
  let : CompactSpace Disk := isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
  let : PreconnectedSpace Disk := isPreconnected_iff_preconnectedSpace.mp
    (convex_closedBall (0 : V2) 1).isPreconnected
  let incoming : Disk × Unit → X := fun z =>
    p (((z.1 : V2) 0, (z.1 : V2) 1), sign * (1 - 2 * (z.2 : ℝ)))
  have incomingCube (z : Disk × Unit) :
      (((z.1 : V2) 0, (z.1 : V2) 1), sign * (1 - 2 * (z.2 : ℝ))) ∈ Cube := by
    refine ⟨disk_pair_coordinates z.1.property, ?_⟩
    rcases hsign with h | h <;> rw [h] <;> constructor <;>
      linarith [z.2.property.1, z.2.property.2]
  have hincoming : Continuous incoming := by
    have hc (i : Fin 2) : Continuous (fun z : Disk × Unit => (z.1 : V2) i) :=
      (continuous_apply i).comp (continuous_subtype_val.comp continuous_fst)
    exact hp.continuousOn.comp_continuous ((hc 0 |>.prodMk (hc 1)).prodMk
      (continuous_const.mul (continuous_const.sub
        (continuous_const.mul (continuous_subtype_val.comp continuous_snd))))) incomingCube
  have hincomingR (z : Disk × Unit) : incoming z ∈ R :=
    hDR (hpimage.subset ⟨_, incomingCube z, rfl⟩)
  have hbase (z : Disk) : incoming (z, ⟨0, by norm_num⟩) ∈ protectedEndpointMap p side '' Disk := by
    refine ⟨z, z.property, ?_⟩
    simp [incoming, protectedEndpointMap, sign]
  have hzero (z : Disk × Unit) : incoming z ∈ protectedEndpointMap p side '' Disk ↔
      (z.2 : ℝ) = 0 := by
    constructor
    · rintro ⟨w, hw, hwz⟩
      have hh := congrArg Prod.snd (hpi (haCube hw) (incomingCube z) hwz)
      change sign = sign * (1 - 2 * (z.2 : ℝ)) at hh
      rcases hsign with h | h <;> rw [h] at hh <;> linarith
    · intro h
      refine ⟨z.1, z.1.property, ?_⟩
      simp [incoming, protectedEndpointMap, h, sign]
  have hcover : D ⊆ (protectedEndpointMap p side '' Disk) ∪ range incoming ∪ (∅ : Set X) := by
    intro x hx
    obtain ⟨z, hz, rfl⟩ := hpimage.symm.subset hx
    let w : V2 := ![z.1.1, z.1.2]
    have hw : w ∈ Disk := by
      rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
      intro i
      fin_cases i
      · exact abs_le.mpr hz.1.1
      · exact abs_le.mpr hz.1.2
    let t : Unit := ⟨(1 - sign * z.2) / 2, by
      rcases hsign with h | h <;> rw [h] <;> constructor <;> linarith [hz.2.1, hz.2.2]⟩
    refine Or.inl (Or.inr ⟨(⟨w, hw⟩, t), ?_⟩)
    apply congrArg p
    apply Prod.ext
    · rfl
    · change sign * (1 - 2 * ((1 - sign * z.2) / 2)) = z.2
      rcases hsign with h | h <;> rw [h] <;> ring
  obtain ⟨P, δ, positive, hPO, hδ, hδhalf, havoid⟩ :=
    Dehn.Annuli.exists_original_proper_disk_opposite_product hR he hjPL hji hjR hjproper
      hO hendO incoming hincoming hincomingR hbase hzero
      (Q := univ) isCompact_univ isClosed_empty (fun _ _ => by simp) hcover
  exact ⟨P, δ, positive, hPO, hδ, hδhalf, fun q t => havoid q (mem_univ _) t⟩

theorem exists_disjoint_outward_products_at_protected_endpoints
    {X α : Type*} [TopologicalSpace X] [T2Space X]
    {e : α → OpenPartialHomeomorph X V3} {R D : Set X}
    (hR : IsCompact R) (he : PLDomain e R) (hDR : D ⊆ R)
    (p : P3 → X) (hp : PolyhedralPLInCharts e p Cube) (hpi : InjOn p Cube)
    (hpimage : p '' Cube = D)
    (hproper : ∀ z ∈ Cube, p z ∈ frontier R ↔ |z.1.1| = 1 ∨ |z.1.2| = 1) :
    ∃ (P : (i : Bool) → OriginalDiskProduct e R (protectedEndpointMap p i))
      (δ : Bool → ℝ) (positive : Bool → Bool),
      Disjoint ((P false).map '' (Disk ×ˢ I)) ((P true).map '' (Disk ×ˢ I)) ∧
      ∀ i, 0 < δ i ∧ δ i ≤ 1 / 2 ∧ ∀ (q : Disk) (t : I),
        (if positive i then (t : ℝ) ∈ Ico (-(δ i)) 0 else (t : ℝ) ∈ Ioc 0 (δ i)) →
          (P i).map ((q : V2), (t : ℝ)) ∉ D := by
  classical
  have hendcube (i : Bool) (z : V2) (hz : z ∈ Disk) :
      ((z 0, z 1), if i then (1 : ℝ) else -1) ∈ Cube := by
    refine ⟨disk_pair_coordinates hz, ?_⟩
    cases i <;> norm_num
  have hc (i : Bool) : IsCompact (protectedEndpointMap p i '' Disk) := by
    apply (isCompact_closedBall _ _).image_of_continuousOn
    exact hp.continuousOn.comp (by fun_prop) (fun z hz => hendcube i z hz)
  have hdis : Disjoint (protectedEndpointMap p false '' Disk) (protectedEndpointMap p true '' Disk) := by
    apply disjoint_left.mpr
    rintro _ ⟨z, hz, rfl⟩ ⟨w, hw, hwz⟩
    have hh := congrArg Prod.snd (hpi (hendcube true w hw) (hendcube false z hz) hwz)
    norm_num at hh
  obtain ⟨P0, δ0, pos0, hP0, hδ0, hδ0half, havoid0⟩ :=
    exists_outward_product_at_protected_endpoint hR he hDR p hp hpi hpimage hproper false
      (hc true).isClosed.isOpen_compl (fun _ hx hy => disjoint_left.mp hdis hx hy)
  have hP0compact : IsCompact (P0.map '' (Disk ×ˢ I)) :=
    ((isCompact_closedBall _ _).prod isCompact_Icc).image_of_continuousOn P0.polyhedral.continuousOn
  have htrueavoid : protectedEndpointMap p true '' Disk ⊆ (P0.map '' (Disk ×ˢ I))ᶜ := by
    rintro _ hx ⟨z, hz, rfl⟩
    exact hP0 hz hx
  obtain ⟨P1, δ1, pos1, hP1, hδ1, hδ1half, havoid1⟩ :=
    exists_outward_product_at_protected_endpoint hR he hDR p hp hpi hpimage hproper true
      hP0compact.isClosed.isOpen_compl htrueavoid
  let P : (i : Bool) → OriginalDiskProduct e R (protectedEndpointMap p i) := Bool.rec P0 P1
  let δ : Bool → ℝ := Bool.rec δ0 δ1
  let positive : Bool → Bool := Bool.rec pos0 pos1
  refine ⟨P, δ, positive, ?_, ?_⟩
  · apply disjoint_left.mpr
    rintro _ hx ⟨z, hz, rfl⟩
    exact hP1 hz hx
  · intro i
    cases i
    · exact ⟨hδ0, hδ0half, havoid0⟩
    · exact ⟨hδ1, hδ1half, havoid1⟩

theorem HamiltonMarkedProtectedBall.exists_original_protected_end_disk_collars
    {ι κ α : Type*} [Fintype ι] [Fintype κ]
    {L : Submodule ℤ (κ → ℝ)} [DiscreteTopology L] [IsZLattice ℝ L]
    {e : α → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) V3}
    {D : Set (LatticeHandleAmbient ι κ L)}
    (b : HamiltonMarkedProtectedBall ι κ L e D)
    (he : PLDomain e (latticeHandleDomain ι κ L))
    (hdim : Fintype.card ι + Fintype.card κ = 3) (hi : Fintype.card ι = 2) :
    ∃ (p : P3 → LatticeHandleAmbient ι κ L) (G : Cube ≃ₜ D)
      (P : (i : Bool) → OriginalDiskProduct e (latticeHandleDomain ι κ L) (protectedEndpointMap p i))
      (δ : Bool → ℝ) (positive : Bool → Bool),
      PolyhedralPLInCharts e p Cube ∧
      (∀ z : Cube, p z = (G z : LatticeHandleAmbient ι κ L)) ∧
      InjOn p Cube ∧ p '' Cube = D ∧
      (∀ z ∈ Cube, p z ∈ frontier D ↔ z ∈ frontier Cube) ∧
      (∀ z ∈ Cube, p z ∈ frontier (latticeHandleDomain ι κ L) ↔ |z.1.1| = 1 ∨ |z.1.2| = 1) ∧
      Disjoint ((P false).map '' (Disk ×ˢ I)) ((P true).map '' (Disk ×ˢ I)) ∧
      ∀ i, 0 < δ i ∧ δ i ≤ 1 / 2 ∧ ∀ (q : Disk) (t : I),
        (if positive i then (t : ℝ) ∈ Ico (-(δ i)) 0 else (t : ℝ) ∈ Ioc 0 (δ i)) →
          (P i).map ((q : V2), (t : ℝ)) ∉ D := by
  obtain ⟨p, G, hp, hval, hpi, himage, hlat, hfront, _⟩ :=
    b.exists_original_protected_ball_product he hdim hi
  have hmark : D ∩ frontier (latticeHandleDomain ι κ L) =
      hamiltonAttachingBlock ι κ L (3 / 2) := by
    rcases b.position with ⟨hzero, _⟩ | ⟨_, _, _, _, _, hm⟩
    · omega
    · exact hm
  have hproper (z : P3) (hz : z ∈ Cube) : p z ∈ frontier (latticeHandleDomain ι κ L) ↔
      |z.1.1| = 1 ∨ |z.1.2| = 1 := by
    have hpD : p z ∈ D := himage.subset ⟨z, hz, rfl⟩
    have hm : p z ∈ frontier (latticeHandleDomain ι κ L) ↔
        p z ∈ hamiltonAttachingBlock ι κ L (3 / 2) := by
      rw [← hmark]
      exact ⟨fun hx => ⟨hpD, hx⟩, fun hx => hx.2⟩
    exact hm.trans (hlat z hz)
  obtain ⟨P, δ, positive, hdis, havoid⟩ := exists_disjoint_outward_products_at_protected_endpoints
    (isCompact_latticeHandleDomain ι κ L) he b.subset_domain p hp hpi himage hproper
  exact ⟨p, G, P, δ, positive, hp, hval, hpi, himage, hfront, hproper, hdis, havoid⟩

end PoincareConjecture.M76
