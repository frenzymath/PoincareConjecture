import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Surfaces.Components.CompressedModel
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Surfaces.TwoBoundaryCount
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Surfaces.RimParametrization.MarkedAnnulus
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Surfaces.RimParametrization.OriginalAtlas









set_option autoImplicit false
open Set Metric Geometry PLAnnularStrip

namespace PoincareConjecture.M76.HamiltonIntervalTorus

local notation "V3" => (Fin 3 → ℝ)
local notation "L" => hamiltonLowerPeriodLattice (Fin 2)
local notation "X" => LatticeHandleAmbient (Fin 1) (Fin 2) L
local notation "R" => latticeHandleDomain (Fin 1) (Fin 2) L
local notation "H" => LatticeHandle (Fin 1) (Fin 2) L
local notation "B" => latticeHandleBoundary (Fin 1) (Fin 2) L
local notation "C" => AddCircle (4 * (128 : ℝ))
local notation "Ann" => squareAnnulus 8 1



theorem exists_compressed_source_annulus_with_original_rims
    {α β : Type*} (e : α → OpenPartialHomeomorph X V3)
    (d : β → OpenPartialHomeomorph X V3)
    (hd : StandardLatticeHandleAtlas (Fin 1) (Fin 2) L d) (phi : C(H, H))
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 1) (Fin 2) L phi))
    (F0 : (ContinuousMap.id H).HomotopyRel phi B)
    {u v : ℝ} {theta theta' : C}
    (heN : PLDomain e (sourceSlab phi u v))
    (hfront : frontier (sourceSlab phi u v) = (sourceSlab phi u v ∩ frontier R) ∪
      (sourceSurface phi theta ∪ sourceSurface phi theta'))
    (hAB : Disjoint (sourceSurface phi theta) (sourceSurface phi theta'))
    (hcorner : ∀ x ∈ sourceSurface phi theta ∩ frontier R,
      ∃ (psi lambda : V3 →ᴬ[ℝ] ℝ) (w z : V3) (G : OpenPartialHomeomorph X V3),
        psi.contLinear w = 1 ∧ psi.contLinear z = 0 ∧ lambda.contLinear z = 1 ∧
        x ∈ G.source ∧ psi (G x) = 0 ∧
        (∀ i, (e i).symm.trans G ∈ piecewiseAffineGroupoid V3) ∧
        (∀ y ∈ G.source, y ∈ sourceSlab phi u v ↔ 0 ≤ psi (G y)) ∧
        (∀ y ∈ G.source, y ∈ sourceSlab phi u v ∩ frontier R ↔
          psi (G y) = 0 ∧ 0 ≤ lambda (G y)) ∧
        ∀ y ∈ G.source, y ∈ sourceSurface phi theta ↔
          psi (G y) = 0 ∧ lambda (G y) ≤ 0)
    (hinj : ∀ x : sourceSurface phi theta, Function.Injective (FundamentalGroup.map
      (⟨Subtype.val, continuous_subtype_val⟩ : C(sourceSurface phi theta, X)) x)) :
    ∃ (S : Set X) (A : Ann ≃ₜ S) (q : ℝ × ℝ → X),
      S ⊆ sourceSurface phi theta ∧
      (∀ x ∈ S, connectedComponentIn (sourceSurface phi theta) x = S) ∧
      PolyhedralPLInCharts e q Ann ∧
      (∀ x : Ann, (A x : X) = q x) ∧
      ∀ side z, (A (Dehn.annulusRimPoint side z) : X) =
        (sourceBoundaryCircle phi theta F0 (originalIntervalEndpoint side)
          (originalIntervalEndpoint_norm side)
          (AddCircle.homeomorphAddCircle (4 * (8 : ℝ)) (4 * (128 : ℝ))
            (by norm_num) (by norm_num) z) : X) := by
  classical
  obtain ⟨s, F, S, K, J, G, g, gamma, delta, hJK, hFc, hF, hFi, hSF,
    hcomponent, hK, hKs, hGF, hGg, hgPL, hpure, hlinks, hconn, hcofaces,
    hdis, hgamma, hdelta, hsource, hrim⟩ :=
    exists_compressed_sourceSurface_common_component_model
      e d hd phi hphi F0 heN hfront hAB hcorner hinj
  obtain ⟨a, ha, hminus, hplus⟩ := exists_annulus_of_generating_boundary
    K hK hpure (by intro w hw; convert! hlinks w hw) hconn J hJK gamma hgamma
      (hdis Bool.false_ne_true)
      hcofaces (delta false 0) (hrim false).1.2 (hrim false).2
  obtain ⟨A, hA, hAv⟩ := exists_annulus_chart_prescribed_source_rims
    hd phi hphi theta F0 F hF hSF G hGF a ha (fun side => (J side).space)
      (fun side => SimplicialComplex.space_subset_of_le (hJK side))
      delta hdelta hsource (by intro side x; cases side; exact hminus x; exact hplus x)
  obtain ⟨q, hq, hqv⟩ := exists_original_atlas_parametrization e A hA G g hgPL hGg
  refine ⟨S, A.trans G, q, hSF, hcomponent, hq, hqv, ?_⟩
  intro side z
  let scale := AddCircle.homeomorphAddCircle (4 * (8 : ℝ)) (4 * (128 : ℝ))
    (by norm_num) (by norm_num)
  let y : S := ⟨sourceBoundaryCircle phi theta F0 (originalIntervalEndpoint side)
    (originalIntervalEndpoint_norm side) (scale z), hsource side (scale z)⟩
  have hy : G.symm y = A (Dehn.annulusRimPoint side z) := by
    apply Subtype.ext
    exact (hGF y).trans (hAv side z).symm
  change (G (A (Dehn.annulusRimPoint side z)) : X) = (y : X)
  rw [← hy, G.apply_symm_apply]

end PoincareConjecture.M76.HamiltonIntervalTorus
