import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.TerminalBoundaryArcJoinedDisk
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.TerminalBoundaryArcSphereClearance
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.SphereExteriorPosition
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.TerminalBoundaryArcDiskRecognition
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Protection.OriginalProtectedExteriorDomain
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Protection.ExteriorFrontierConnected
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.TerminalBoundaryArcPolygonRegion
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.TerminalBoundaryArcEndTopology
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.TerminalEndFrontier
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.OriginalLabeledEndEmbedding










set_option autoImplicit false
open Set Metric Geometry PLAnnularStrip
open PoincareConjecture.M76.Dehn.Annuli.BoundaryUnionDisk
namespace PoincareConjecture.M76
local notation "P2" => (ℝ × ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Ann" => squareAnnulus 8 1
local notation "CY" => sphere (0 : Fin 2 → ℝ) 1
local notation "J" => Icc (-1 : ℝ) 1
local notation "I" => Icc (0 : ℝ) 1

theorem HamiltonMarkedProtectedBall.exists_original_terminal_disk_union
    {ι κ α : Type*} [Fintype ι] [Fintype κ]
    {L : Submodule ℤ (κ → ℝ)} [DiscreteTopology L] [IsZLattice ℝ L]
    {e : α → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) V3}
    {D : Set (LatticeHandleAmbient ι κ L)}
    (b : HamiltonMarkedProtectedBall ι κ L e D)
    (he : PLDomain e (latticeHandleDomain ι κ L))
    (hdim : Fintype.card ι + Fintype.card κ = 3) (hi : Fintype.card ι = 1)
    (p : P2 → LatticeHandleAmbient ι κ L)
    (hp : PolyhedralPLInCharts e p Ann) (hpi : InjOn p Ann)
    (hfront : p '' Ann ⊆ frontier D)
    (hfull : frontier D ∩ interior (latticeHandleDomain ι κ L) ⊆ p '' Ann)
    (hint : p '' {z | -1 < depth 8 z ∧ depth 8 z < 1} ⊆
      interior (latticeHandleDomain ι κ L))
    (hends : ∀ z : Ann, p z ∈ frontier (latticeHandleDomain ι κ L) ↔
      depth 8 (z : P2) = -1 ∨ depth 8 (z : P2) = 1)
    {n : ℕ} (P : Polygon P2 (n+3)) (hP : P.HasSimplicialEdges)
    (hPi : Function.Injective P)
    (hdepth : ∀ x ∈ P.boundary ℝ, -1 < depth 8 x ∧ depth 8 x < 1)
        (hencl : Dehn.annulusSquare 8 1 ⊆ P.inside)
    {S : Set (LatticeHandleAmbient ι κ L)} (s : ChartwisePLSphere e S)
    {A U C : Set P2} {f : P2 → LatticeHandleAmbient ι κ L}
    {u0 u1 c d : P2} (hA : IsFinitePLBallPair P2 A (U ∪ C))
    (hU : IsFinitePLBallPair ℝ U {u0,u1}) (hC : IsFinitePLBallPair ℝ C {u0,u1})
    (hUC : U ∩ C = {u0,u1}) (hu : u0 ≠ u1)
    (hf : PolyhedralPLInCharts e f A) (hfi : InjOn f A)
    (hS : f '' A ∩ S = f '' C)
    (hF : f '' A ∩ frontier (closure (latticeHandleDomain ι κ L \ D)) = f '' U)
    (hPS : p '' P.boundary ℝ ⊆ S)
    (hc : c ∈ P.boundary ℝ) (hd : d ∈ P.boundary ℝ) (hcd : c ≠ d)
    (h0 : f u0 = p c) (h1 : f u1 = p d)
    (hinter : f '' U ∩ p '' P.boundary ℝ = {f u0,f u1})
    (hSR : S ⊆ interior (latticeHandleDomain ι κ L))
    (m : ℕ) (ns : Fin m → ℕ) (Ps : ∀ i, Polygon P2 (ns i+3)) (k : Fin m)
    (hPk : (Ps k).boundary ℝ = P.boundary ℝ)
    (hcontacts : p '' (⋃ i, (Ps i).boundary ℝ) = S ∩ frontier D)
    (hPs : ∀ i, Function.Injective (Ps i) ∧ (Ps i).HasSimplicialEdges)
    (hdisjoint : Pairwise (fun i j => Disjoint ((Ps i).boundary ℝ) ((Ps j).boundary ℝ)))
    (hstrict : ∀ i x, x ∈ (Ps i).boundary ℝ →
      -1 < depth 8 x ∧ depth 8 x < 1)
    (henclosing : ∀ i, Dehn.annulusSquare 8 1 ⊆ (Ps i).inside)
    (hAE : f '' A ⊆ closure (latticeHandleDomain ι κ L \ D)) :
    let E := closure (latticeHandleDomain ι κ L \ D)
    ∃ V W : Set P2, IsFinitePLBallPair ℝ V {c,d} ∧ IsFinitePLBallPair ℝ W {c,d} ∧
      V ∪ W = P.boundary ℝ ∧ V ∩ W = {c,d} ∧
      ∃ Z : Set P2, (Z = V ∨ Z = W) ∧
      ∃ j : (Fin 2 → ℝ) → LatticeHandleAmbient ι κ L,
        PolyhedralPLInCharts e j (closedBall 0 1) ∧ InjOn j (closedBall 0 1) ∧
        j '' closedBall 0 1 ⊆ frontier E ∧
        j '' sphere 0 1 = f '' U ∪ p '' Z ∧
        j '' closedBall 0 1 ∩ S = p '' Z ∧
        f '' A ∩ j '' closedBall 0 1 = f '' U ∧
        ∃ g : P2 → LatticeHandleAmbient ι κ L,
          PolyhedralPLInCharts e g whole ∧ InjOn g whole ∧
          g '' whole = f '' A ∪ j '' closedBall 0 1 ∧
          g '' frontier whole = f '' C ∪ p '' Z ∧
          g '' whole ⊆ E ∧ g '' whole ∩ S = g '' frontier whole ∧
          g '' whole ∩ frontier E = j '' closedBall 0 1 := by
  intro E
  obtain ⟨V,W,hV,hW,hVW,hVWint,Z,hZchoice,j,hj,hji,hjF,hjr,hjS,hAj⟩ :=
    b.exists_original_terminal_polygon_disk_with_sphere_clearance he hdim hi p hp hpi
      hfront hfull hint hends P hP hPi hdepth hencl s hA hU hC hUC hu hf hfi
      hS hF hPS hc hd hcd h0 h1 hinter hSR m ns Ps k hPk hcontacts hPs hdisjoint
      hstrict henclosing
  have hZ : IsFinitePLBallPair ℝ Z {c,d} := hZchoice.elim
    (fun h => h.symm ▸ hV) (fun h => h.symm ▸ hW)
  have hZP : Z ⊆ P.boundary ℝ := by
    rcases hZchoice with rfl | rfl
    · exact subset_union_left.trans hVW.subset
    · exact subset_union_right.trans hVW.subset
  have hZAnn : Z ⊆ Ann := fun z hz => mem_squareAnnulus_iff_depth.mpr
    ⟨(hdepth z (hZP hz)).1.le,(hdepth z (hZP hz)).2.le⟩
  have hpZ : PolyhedralPLInCharts e p Z := by
    obtain ⟨_,_,_,_,_,_,⟨_,⟨K,hK,hKs,_⟩,_⟩,_⟩ := hZ
    exact hKs ▸ hp.restrict_finite K hK (hKs.subset.trans hZAnn)
  have hUZ : f '' U ∩ p '' Z = {f u0,f u1} := by
    apply Subset.antisymm
    · exact (inter_subset_inter_right _ (image_mono hZP)).trans hinter.subset
    · intro x hx
      rcases mem_insert_iff.mp hx with rfl | hx
      · exact ⟨mem_image_of_mem f (hU.1 (by simp)),⟨c,hZ.1 (by simp),h0.symm⟩⟩
      · rw [mem_singleton_iff] at hx
        subst x
        exact ⟨mem_image_of_mem f (hU.1 (by simp)),⟨d,hZ.1 (by simp),h1.symm⟩⟩
  obtain ⟨g,hg,hgi,hgimage,hgrim,hgE,hgS,hgF⟩ :=
    exists_original_terminal_joined_disk he.compatible isClosed_closure hA hU hC hUC hu
      hZ hf hfi hpZ (hpi.mono hZAnn) hj hji h0 h1 hjr hUZ hAj hS hjS hAE hjF hF
  exact ⟨V,W,hV,hW,hVW,hVWint,Z,hZchoice,j,hj,hji,hjF,hjr,hjS,hAj,
    g,hg,hgi,hgimage,hgrim,hgE,hgS,hgF⟩

end PoincareConjecture.M76

