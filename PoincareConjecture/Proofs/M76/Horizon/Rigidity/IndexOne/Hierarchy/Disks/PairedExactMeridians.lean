import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Hierarchy.Disks.PairedMeridians
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Hierarchy.Disks.ExactMeridian
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Hierarchy.Bands.MarkedProduct









set_option autoImplicit false
open Set Metric Geometry PLAnnularStrip

namespace PoincareConjecture.M76.HamiltonIntervalTorus

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "Q" => sphere (0 : V2) 1
local notation "I" => Icc (-1 : ℝ) 1
local notation "L" => hamiltonLowerPeriodLattice (Fin 2)
local notation "X" => LatticeHandleAmbient (Fin 1) (Fin 2) L
local notation "R" => latticeHandleDomain (Fin 1) (Fin 2) L
local notation "H" => LatticeHandle (Fin 1) (Fin 2) L
local notation "B" => latticeHandleBoundary (Fin 1) (Fin 2) L
local notation "p" => (4 * (128 : ℝ))
local notation "C" => AddCircle p
local notation "Ann" => squareAnnulus 8 1



structure ExactSlabMeridian {α β : Type*}
    {e : α → OpenPartialHomeomorph X V3}
    {d : β → OpenPartialHomeomorph X V3} {phi : C(H, H)}
    (M : PairedMeridianHierarchy e d phi) (uv : ℝ × ℝ) where
  ordered : uv.1 < uv.2
  short : uv.2 < uv.1 + p
  frontierMap : frontier (sourceSlab M.eta uv.1 uv.2) ≃ₜ
    frontier (sourceSlab (ContinuousMap.id H) uv.1 uv.2)
  fixed_old : ∀ x : frontier (sourceSlab M.eta uv.1 uv.2),
    (x : X) ∈ frontier R → (frontierMap x : X) = x
  annulus_marks : ∀ theta (htheta : theta ∈ ({(M.a : C), (M.b : C)} : Set C))
    (x : sourceSurface M.eta theta) (hx : (x : X) ∈ frontier (sourceSlab M.eta uv.1 uv.2)),
    (frontierMap ⟨x, hx⟩ : X) = standardTargetAnnulus theta ((M.annuli theta htheta).symm x)
  frontier_homotopy : (M.eta.comp (slabFrontierHandleInclusion M.eta uv.1 uv.2)).HomotopyRel
    ((slabFrontierHandleInclusion (ContinuousMap.id H) uv.1 uv.2).comp
      ⟨frontierMap, frontierMap.continuous⟩) {x | (x : X) ∈ frontier R}
  bandParameter : V2 × ℝ → X
  band_pl : PolyhedralPLInCharts e bandParameter (Q ×ˢ I)
  band_exact : ∀ z : Q ×ˢ I,
    (sourceMeridianBandCylinder ordered short frontierMap z : X) = bandParameter z
  disk : V2 → X
  disk_pl : PolyhedralPLInCharts e disk D
  disk_embedded : Topology.IsEmbedding (fun z : D => disk z)
  disk_inside : MapsTo disk D (sourceSlab M.eta uv.1 uv.2)
  disk_proper : ∀ z : D, disk z ∈ frontier (sourceSlab M.eta uv.1 uv.2) ↔ (z : V2) ∈ Q
  disk_rim : ∀ z : Q, disk z =
    (cylinderZeroSection (sourceMeridianBandCylinder ordered short frontierMap) z : X)
  width : ℝ
  width_pos : 0 < width
  width_small : width ≤ 1 / 2
  product : OriginalDiskProduct e (sourceSlab M.eta uv.1 uv.2) disk
  product_marks : ∀ z ∈ Q, ∀ t ∈ I, product.map (z, t) = bandParameter (z, width * t)
  product_open : ∀ v : ℝ, 0 < v → v ≤ 1 →
    IsOpen ((Subtype.val : sourceSlab M.eta uv.1 uv.2 → X) ⁻¹'
      (product.map '' (D ×ˢ Ioo (-v) v))) ∧
    IsOpen ((Subtype.val : frontier (sourceSlab M.eta uv.1 uv.2) → X) ⁻¹'
      (product.map '' (Q ×ˢ Ioo (-v) v)))



theorem PairedMeridianHierarchy.exists_exact_meridian
    {α β : Type*} {e : α → OpenPartialHomeomorph X V3}
    {d : β → OpenPartialHomeomorph X V3} {phi : C(H, H)}
    (M : PairedMeridianHierarchy e d phi)
    (hd : StandardLatticeHandleAtlas (Fin 1) (Fin 2) L d)
    (uv : ℝ × ℝ) (huv : uv ∈ ({(M.a, M.b), (M.b, M.a + p)} : Set (ℝ × ℝ))) :
    Nonempty (ExactSlabMeridian M uv) := by
  classical
  let : T2Space X := ((Homeomorph.refl (Fin 1 → ℝ)).prodCongr
    (hamiltonLowerLatticePiEquiv (Fin 2))).isEmbedding.t2Space
  have ha0 : 0 < M.a := by linarith [M.a_range.1]
  have hab : M.a < M.b := by linarith [M.a_range.2, M.b_range.1]
  have hbp : M.b < p := by linarith [M.b_range.2]
  have hphases : ({(uv.1 : C), (uv.2 : C)} : Set C) = {(M.a : C), (M.b : C)} := by
    rcases huv with rfl | rfl
    · rfl
    · simp only [AddCircle.coe_add_period]
      exact pair_comm _ _
  have hc : ∃ c : ℝ, c < uv.1 ∧ uv.1 < uv.2 ∧ uv.2 < c + p := by
    rcases huv with rfl | rfl
    · exact ⟨0, ha0, hab, by simpa using hbp⟩
    · refine ⟨(M.a + M.b) / 2, ?_, ?_, ?_⟩ <;> dsimp <;> linarith
  obtain ⟨c, hca, huvlt, hvc⟩ := hc
  have hshort : uv.2 < uv.1 + p := by linarith
  let Auv : ∀ theta ∈ ({(uv.1 : C), (uv.2 : C)} : Set C),
      Ann ≃ₜ sourceSurface M.eta theta :=
    fun theta htheta => M.annuli theta (hphases ▸ htheta)
  let quv : ∀ theta ∈ ({(uv.1 : C), (uv.2 : C)} : Set C), ℝ × ℝ → X :=
    fun theta htheta => M.parametrizations theta (hphases ▸ htheta)
  obtain ⟨E, hfix, hphase, ⟨G⟩, _⟩ := M.meridians uv huv
  have hinj := M.geometry.slab_ambient_pi1_injective M.identity_homotopy ha0 hab hbp uv huv
  obtain ⟨q, j, hq, hcq, hj, hji, hjN, hproper, hrim⟩ :=
    exists_exact_source_slab_meridian hd M.eta M.original_pl M.identity_homotopy
      hca huvlt hvc (M.geometry.domains uv huv) hinj (M.geometry.frontiers uv huv)
      Auv quv (fun theta htheta => M.parametrizations_pl theta (hphases ▸ htheta))
      (fun theta htheta => M.annuli_exact theta (hphases ▸ htheta)) E hfix
      (fun theta htheta x hx => hphase theta (hphases ▸ htheta) ⟨x, hx⟩ x.property) G
  have hopen : IsOpen ((Subtype.val : frontier (sourceSlab M.eta uv.1 uv.2) → X) ⁻¹'
      cylinderBandInterior (sourceMeridianBandCylinder huvlt hshort E)) := by
    apply pulledBackBandInterior_isOpen
    rw [standardMeridianBand_interior_eq]
    exact isOpen_standardMeridianOpenBand uv.1 uv.2 huvlt hshort
  obtain ⟨w, hw, hws, P, hPmarks, hPopen⟩ :=
    exists_original_cylindrical_band_marked_product (M.geometry.domains uv huv)
      (sourceSlab_isCompact M.eta uv.1 uv.2) (sourceMeridianBandCylinder huvlt hshort E)
      (frontierBandPullback_subset E) q hq hcq hopen j hj hji hjN hproper hrim
  exact ⟨{
    ordered := huvlt, short := hshort, frontierMap := E, fixed_old := hfix
    annulus_marks := hphase, frontier_homotopy := G
    bandParameter := q, band_pl := hq, band_exact := hcq
    disk := j, disk_pl := hj, disk_embedded := hji, disk_inside := hjN
    disk_proper := hproper, disk_rim := hrim
    width := w, width_pos := hw, width_small := hws, product := P
    product_marks := hPmarks, product_open := hPopen }⟩



theorem exists_original_paired_exact_meridians
    {α β : Type*} (e : α → OpenPartialHomeomorph X V3)
    (d : β → OpenPartialHomeomorph X V3)
    (hd : StandardLatticeHandleAtlas (Fin 1) (Fin 2) L d)
    (phi : C(H, H))
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 1) (Fin 2) L phi))
    (hI : IsPLIrreducible e R)
    (F0 : (ContinuousMap.id H).HomotopyRel phi B) :
    ∃ M : PairedMeridianHierarchy e d phi,
      ∀ uv ∈ ({(M.a, M.b), (M.b, M.a + p)} : Set (ℝ × ℝ)),
        Nonempty (ExactSlabMeridian M uv) := by
  obtain ⟨M⟩ := exists_original_paired_meridian_hierarchy e d hd phi hphi hI F0
  exact ⟨M, fun uv huv => M.exists_exact_meridian hd uv huv⟩

end PoincareConjecture.M76.HamiltonIntervalTorus
