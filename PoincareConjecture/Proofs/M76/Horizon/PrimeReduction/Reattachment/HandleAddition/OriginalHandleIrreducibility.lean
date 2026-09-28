import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.OriginalSpanningBigon
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.OriginalSpanningCrossings
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.SpanningContactMinimum

set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set Metric Geometry Topology PLAnnularStrip
namespace PoincareConjecture.M76
local notation "P2" => (ℝ × ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)
local notation "Ann" => squareAnnulus 8 1

theorem HamiltonMarkedProtectedBall.isPLIrreducible_handle_of_exterior
    {ι κ α : Type*} [Fintype ι] [Fintype κ]
    {L : Submodule ℤ (κ → ℝ)} [DiscreteTopology L] [IsZLattice ℝ L]
    {e : α → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) V3}
    {D : Set (LatticeHandleAmbient ι κ L)}
    (b : HamiltonMarkedProtectedBall ι κ L e D)
    (he : PLDomain e (latticeHandleDomain ι κ L))
    (hdim : Fintype.card ι + Fintype.card κ = 3) (hi : Fintype.card ι = 1)
    (hI : IsPLIrreducible e (closure (latticeHandleDomain ι κ L \ D))) :
    IsPLIrreducible e (latticeHandleDomain ι κ L) := by
  classical
  refine ⟨he,?_⟩
  intro S hSR ⟨s⟩
  by_contra hn
  let X := LatticeHandleAmbient ι κ L
  let R := latticeHandleDomain ι κ L
  let E := closure (R \ D)
  obtain ⟨d,hd,_,hmin,_,hann,hplan⟩ :=
    b.exists_minimal_nonbounding_sphere_exterior_position he hdim hi hI s hSR hn
  obtain ⟨⟨s₀⟩,hSR₀,hn₀,hDQ,hQ,hCQ,hG,hGs,hpres,hGc,hdegree,hcross⟩ := hd
  obtain ⟨pAnn,m,n,P,hpAnn,hpAi,hfamily,hP,hdis,hdepth,hfront,hfull,hint,hends,hencl,_⟩ := hann
  obtain ⟨K,B,p,hK,_,hp,hpi,hps,_,hpp,_⟩ := hplan
  obtain ⟨f,hf,hfmin,hfmodel,J,hJ,hJs,hJball,hfPL,hfi,hfE,hfproper,hfbc,hfic,
      hfno,C,M,harcs,hreturn,k,A,U,u0,u1,hu,hA,hU,hC,hAJ,hfA,hfiA,hAE,
      hAq,hUC,hAS,hAF,hAI,i,j,c,d₀,hc,hd₀,hcd,h0,h1,hspan,hproduct⟩ :=
    b.exists_circle_free_minimal_essential_disk_with_spanning_bigon he hdim hi hI
      s₀ hSR₀ hn₀ d.2.1 d.2.2 hDQ hQ hCQ hG hGs hpres hGc hdegree hcross hmin
      K hK p hp hpi hps hpp pAnn hpAnn hpAi n P hfamily hP hdis hdepth
      hfront hfull hint hends hencl
  let a := ContinuousLinearEquiv.finTwoArrow ℝ ℝ
  have hER : E ⊆ R := closure_minimal sdiff_subset he.closed
  have hAR : (f ∘ a.symm) '' A ⊆ interior R := by
    rintro _ ⟨z,hz,rfl⟩
    by_cases hzU : z ∈ U
    · exact hspan.2.1 ⟨z,hzU,rfl⟩
    by_cases hzC : z ∈ M.pieces k
    · exact hSR₀ (hAS.symm.subset ⟨z,hzC,rfl⟩).2
    · exact interior_mono hER (hAI ⟨z,⟨hz,fun h => h.elim hzU hzC⟩,rfl⟩).1
  obtain ⟨W,H,j₀,T,hW,hWS,_,_,hNfront,_,_,_,hH,hj₀,hHrim,hPO,_,hjU,hjC,hmark,_⟩ :=
    hproduct (interior R) isOpen_interior hAR
  have hcrossO : ∀ x ∈ d.1 ∩ frontier E,∃ Q₀ : OpenPartialHomeomorph X V3,
      x ∈ Q₀.source ∧ Q₀ x = 0 ∧
      (∀ a,(e a).symm.trans Q₀ ∈ piecewiseAffineGroupoid V3) ∧
      (∀ y ∈ Q₀.source,y ∈ d.1 ↔ Q₀ y 1 = 0) ∧
      ∀ y ∈ Q₀.source,y ∈ frontier E ↔ Q₀ y 0 = 0 := by
    intro x hx
    obtain ⟨Q₀,hxQ,_,_,hQ0,hQPL,_,hQS,hQE⟩ :=
      hcross (d.2.1 x) (hGs.symm.subset (mem_image_of_mem d.2.1 hx))
        univ isOpen_univ (mem_univ _)
    exact compatible_paired_chart_of_coordinate_crossing d.2.1 hQ Q₀ hQPL
      (hCQ hx) hxQ hQ0 hQS hQE
  obtain ⟨S',r,⟨s'⟩,hSR',hn',hr,hri,hrFD,hr0,hr1,htrace,hnew,hcross'⟩ :=
    b.exists_original_spanning_replacement_with_crossings he hdim hi s₀ hSR₀ hn₀
      hW hWS hcrossO T hNfront hPO hA hU hC hu hUC H hH hHrim hj₀ hjU hjC hmark
  have hcontacts : d.1 ∩ frontier E = d.1 ∩ frontier D := by
    ext x
    exact and_congr_right (fun hx => b.frontier_exterior_iff_interior he hdim hi (hSR₀ hx))
  have hPA : ∀ i,(P i).boundary ℝ ⊆ Ann := by
    intro i z hz
    exact mem_squareAnnulus_iff_depth.mpr ⟨(hdepth i z hz).1.le,(hdepth i z hz).2.le⟩
  exact not_spanning_replacement_of_minimal_position he s' hSR' hn' d.2.1 hDQ hQ
    pAnn hpAnn hpAi (hfront.trans b.ball.boundary_subset) n P hP hPA hdis
    (hfamily.trans hcontacts.symm) d.2.2 hGs i j hspan.1 r hr hri
    (hrFD.trans inter_subset_right) htrace
    (by rw [hr0,h0]; exact mem_image_of_mem pAnn hc)
    (by rw [hr1,h1]; exact mem_image_of_mem pAnn hd₀) hnew hcross' hmin

end PoincareConjecture.M76
