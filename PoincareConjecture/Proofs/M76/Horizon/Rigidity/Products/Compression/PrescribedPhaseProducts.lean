import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.Compression.PhaseProducts
import PoincareConjecture.Proofs.M76.Rigidity.OriginalClosedSlabPreservation

set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "H0" => LatticeHandle (Fin 0) (Fin 3) L0
local notation "B0" => latticeHandleBoundary (Fin 0) (Fin 3) L0
local notation "C0" => AddCircle (4 * (16 : ℝ))
local notation "Q0" => hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates

open Classical in

theorem exists_hamiltonZero_prescribed_phase_products {ι κ : Type*}
    (e : ι → OpenPartialHomeomorph X0 V3)
    (d : κ → OpenPartialHomeomorph X0 V3)
    (hd : StandardLatticeHandleAtlas (Fin 0) (Fin 3) L0 d)
    (phi : C(H0, H0))
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 phi))
    (F : (ContinuousMap.id H0).HomotopyRel phi B0)
    (a b : ℝ) (ha : 0 < a) (hab : a < b) (hb : b < 4 * 16)
    (he : PLDomain e ((hamiltonZeroCircleMap phi) ⁻¹'
      AddCircle.closedIntervalArc (4 * 16) a b))
    (hfront : frontier ((hamiltonZeroCircleMap phi) ⁻¹'
      AddCircle.closedIntervalArc (4 * 16) a b) =
      (hamiltonZeroCircleMap phi) ⁻¹' {(a : C0), (b : C0)}) :
    ∃ psi : C(H0, H0),
      ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 psi) ∧
      Nonempty (phi.HomotopyRel psi B0) ∧
      Nonempty ((ContinuousMap.id H0).HomotopyRel psi B0) ∧
      let q := hamiltonZeroCircleMap phi
      let q' := hamiltonZeroCircleMap psi
      let A := AddCircle.closedIntervalArc (4 * 16) a b
      let R := q ⁻¹' A
      q' ⁻¹' {(a : C0)} = q ⁻¹' {(a : C0)} ∧
      q' ⁻¹' {(b : C0)} = q ⁻¹' {(b : C0)} ∧
      q' ⁻¹' A = R ∧ q' ⁻¹' interior A = interior R ∧
      q' ⁻¹' (interior A)ᶜ = (interior R)ᶜ ∧
      ∃ (s : Finset R) (rho : ℝ), 0 < rho ∧
        ∀ theta ∈ ({a, b} : Set ℝ),
          ∃ (J : SimplicialComplex ℝ (s → ℝ × V3))
            (H : J.space ≃ₜ (q ⁻¹' {(theta : C0)} : Set X0))
            (c : (s → ℝ × V3) × ℝ → X0)
            (K : SimplicialComplex ℝ ((s → ℝ × V3) × ℝ)),
            J.faces.Finite ∧ K.faces.Finite ∧
            K.space = J.space ×ˢ Icc (-rho) rho ∧
            PolyhedralPLInCharts e c K.space ∧
            Topology.IsEmbedding (fun z : K.space => c z) ∧
            (∀ x : J.space, c ((x : s → ℝ × V3), 0) = H x) ∧
            (∀ eps : ℝ, 0 < eps → eps ≤ rho →
              IsOpen (c '' (J.space ×ˢ Ioo (-eps) eps))) ∧
            (∀ x ∈ J.space, ∀ t ∈ Icc (-rho) rho,
              q' (c (x, t)) = (theta : C0) +
                (((if theta = a then 1 else -1) * t : ℝ) : C0)) ∧
            q' ⁻¹' AddCircle.closedIntervalArc (4 * 16) (theta - rho) (theta + rho) =
              c '' K.space := by
  let : Fact (0 < 4 * (16 : ℝ)) := ⟨by norm_num⟩
  obtain ⟨hSa, hna, hSb, hnb, hdisjoint, hR, he', hfront', hminus,
    heminus, hfrontminus, hne, hneminus,
    eta, heta, haeta, habeta, hbeta, hfamily⟩ :=
    PrescribedSlab.exists_hamiltonZero_adjusted_phase_products
      e d hd phi hphi F a b ha hab hb he hfront
  obtain ⟨s, L, HB, c, hL, hc, hi, hbase, hmarks,
    delta, hdelta, hdeltaHalf, hcU, hcA, hopen,
    v, hvc, hval, hperiod, hlabels, hsigns,
    r, hr, hwidth, hrEta, D, w, G,
    hDzero, hDvalue, hDfixed, hDS, hDout, hDbase, hDends, hDinner,
    hwzero, hwvalue, hwfixed, hwS, hwout, hwbase, hwends, hwbound, hwinner,
    hGvalue, hGzero, hGS, hGout, hGfixed, hGinner, hlevels, hparameter, hendpoint,
    rho, hrho, hrhor, hpre, hpreA, hpreB, hproducts⟩ :=
    hfamily univ isOpen_univ (subset_univ _)
  let g : C(X0, X0) := ⟨fun y => G (1, y),
    G.continuous.comp (continuous_const.prodMk continuous_id)⟩
  let psi := hamiltonZeroHandleMap g
  have hpsi : ChartwisePLMap e d
      (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 psi) := by
    rw [hamiltonZeroHandleMap_domain]
    exact hendpoint
  let H := hamiltonZeroHandleHomotopy phi G hGzero
  have hcircle (y : X0) : hamiltonZeroCircleMap psi y = (Q0 (G (1, y))).2 := by
    rw [← hamiltonZeroAmbientMap_circle psi y]
    rw [hamiltonZeroAmbientMap_handle]
    rfl
  have hcircleFun : (hamiltonZeroCircleMap psi : X0 → C0) =
      (fun y => (Q0 (G (1, y))).2) := funext hcircle
  obtain ⟨hside, hinterior, hexterior⟩ :=
    hamiltonZero_slab_side_preimages phi ha hab hb hfront G hGzero hlevels 1
  refine ⟨psi, hpsi, ⟨H⟩, ⟨F.trans H⟩, ?_⟩
  dsimp only
  rw [hcircleFun]
  refine ⟨(hlevels 1).1, (hlevels 1).2, hside, hinterior, hexterior,
    s, rho, hrho, ?_⟩
  intro theta htheta
  obtain ⟨J, HJ, K, hJ, hJL, hJs, hHJ, hzero, hK, hKs, hcK, hiK,
    hJopen, hKpre⟩ := hproducts theta htheta
  refine ⟨J, HJ, c, K, hJ, hK, hKs, hcK, hiK, fun x => (hHJ x).symm,
    fun eps heps hepsrho => hJopen eps heps (hepsrho.trans (by linarith)), ?_, hKpre⟩
  intro x hx t ht
  have hxL : x ∈ L.space := (SimplicialComplex.space_subset_of_le hJL) hx
  have hlabel : hamiltonZeroCircleMap phi (c (x, 0)) = (theta : C0) := by
    have h := hx
    rw [hJs] at h
    exact h.2
  have htR : (x, t) ∈ L.space ×ˢ Icc (-r) r :=
    ⟨hxL, (neg_le_neg hrhor.le).trans ht.1, ht.2.trans hrhor.le⟩
  have hnormal := congrArg Prod.snd (hGinner (x, t) htR)
  dsimp only at hnormal
  rw [hlabel] at hnormal
  have hphase : ((theta : C0) = (a : C0)) ↔ theta = a := by
    constructor
    · intro heq
      apply (AddCircle.coe_eq_coe_iff_of_mem_Ico (p := 4 * (16 : ℝ))
        (a := (0 : ℝ)) ?_ ?_).mp heq
      · rcases htheta with rfl | rfl <;> constructor <;> linarith
      · constructor <;> linarith
    · exact congrArg ((↑) : ℝ → C0)
  simpa only [hphase] using hnormal

end PoincareConjecture.M76
