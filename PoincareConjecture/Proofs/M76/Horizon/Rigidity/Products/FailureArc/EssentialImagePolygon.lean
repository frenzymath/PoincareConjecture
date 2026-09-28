import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.RimEssentiality
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.MarkedSquareImageCycle
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.GeometricCyclePolygon
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.PolygonCycleLoopComparison
import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Topology.LoopClassTransport











set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76

open Dehn

local notation "V2" => (Fin 2 → ℝ)
local notation "Q2" => sphere (0 : V2) 1



theorem exists_essential_polygon_in_marked_rim
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E] [TopologicalSpace X]
    {a : V2 → E} (ha : FinitePiecewiseAffineOn a Q2)
    (gamma : C(Q2, X)) (hgamma : ¬ gamma.Nullhomotopic)
    (j : C(a '' Q2, X))
    (hj : ∀ x : Q2, j ⟨a x, mem_image_of_mem a x.property⟩ = gamma x) :
    ∃ (n : ℕ) (P : Polygon E (n + 3)) (hsub : P.boundary ℝ ⊆ a '' Q2),
      Function.Injective P ∧ P.HasSimplicialEdges ∧
      ¬ (j.comp (ContinuousMap.inclusion hsub)).Nullhomotopic := by
  classical
  let p := Path.refl (gamma squareRimBase)
  let J : Subgroup (FundamentalGroup X (gamma squareRimBase)) := ⊥
  have houtside : p.whiskeredLoopClass (squareRimLoop.map gamma.continuous) ∉ J := by
    intro h
    have hclass := (p.whiskeredLoopClass_eq_one_iff _).mp (Subgroup.mem_bot.mp h)
    exact hgamma (nullhomotopic_of_squareRimLoop gamma (Path.Homotopic.Quotient.eq.mp hclass))
  obtain ⟨K, himage, G, _, hG, _, _, v, c, q, hc, hout⟩ :=
    exists_marked_square_image_cycle ha gamma j hj p J houtside
  obtain ⟨n, P, hlen, hvertices, hbase, hinj, hP, _, hPK⟩ :=
    K.exists_polygon_of_geometric_cycle c hc
  let inc : C(P.boundary ℝ, K.space) := ContinuousMap.inclusion hPK
  have hcomp : G.comp inc = j.comp (ContinuousMap.inclusion (hPK.trans himage)) := by
    ext x
    exact hG (inc x)
  refine ⟨n, P, hPK.trans himage, hinj, hP, ?_⟩
  intro hn
  have hnull : (G.comp inc).Nullhomotopic := hcomp.symm ▸ hn
  have hpnull := Path.Homotopic.map_nullhomotopic_of_nullhomotopic hnull P.boundaryLoop
  have hloop := (K.polygon_boundaryLoop_homotopic_geometricWalk
    c P hlen hvertices hbase hPK).map G
  have hbaseK : (⟨v, K.vertices_subset_space v.property⟩ : K.space) =
      inc ⟨P 0, P.vertex_mem_boundary 0⟩ := Subtype.ext hbase.symm
  have hcast := hpnull.pathCast (congrArg G hbaseK) (congrArg G hbaseK)
  have hselected : ((K.geometricWalkPath c).map G.continuous).Homotopic
      (Path.refl (G ⟨v, K.vertices_subset_space v.property⟩)) := by
    apply hloop.symm.trans
    convert hcast using 1
    · ext t
      rfl
    · ext t
      exact congrArg G hbaseK
  apply hout
  exact Subgroup.mem_bot.mpr ((q.whiskeredLoopClass_eq_one_iff _).mpr
    (Path.Homotopic.Quotient.eq.mpr hselected))

end PoincareConjecture.M76
