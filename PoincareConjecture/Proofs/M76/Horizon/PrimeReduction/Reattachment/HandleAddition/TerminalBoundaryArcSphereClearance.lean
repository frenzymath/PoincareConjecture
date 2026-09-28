import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.TerminalBoundaryArcClearDisk
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
namespace PoincareConjecture.M76
local notation "P2" => (ℝ × ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Ann" => squareAnnulus 8 1
local notation "CY" => sphere (0 : Fin 2 → ℝ) 1
local notation "J" => Icc (-1 : ℝ) 1
local notation "I" => Icc (0 : ℝ) 1

theorem HamiltonMarkedProtectedBall.exists_original_terminal_polygon_disk_with_sphere_clearance
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
    (henclosing : ∀ i, Dehn.annulusSquare 8 1 ⊆ (Ps i).inside) :
    let E := closure (latticeHandleDomain ι κ L \ D)
    ∃ V W : Set P2, IsFinitePLBallPair ℝ V {c,d} ∧ IsFinitePLBallPair ℝ W {c,d} ∧
      V ∪ W = P.boundary ℝ ∧ V ∩ W = {c,d} ∧
      ∃ Z : Set P2, (Z = V ∨ Z = W) ∧
      ∃ j : (Fin 2 → ℝ) → LatticeHandleAmbient ι κ L,
        PolyhedralPLInCharts e j (closedBall 0 1) ∧ InjOn j (closedBall 0 1) ∧
        j '' closedBall 0 1 ⊆ frontier E ∧
        j '' sphere 0 1 = f '' U ∪ p '' Z ∧
        j '' closedBall 0 1 ∩ S = p '' Z ∧
        f '' A ∩ j '' closedBall 0 1 = f '' U := by
  classical
  intro E
  let X := LatticeHandleAmbient ι κ L
  obtain ⟨V,W,hV,hW,hVW,hVWint,j,hj,hji,hjF,hjr,hjP,hclear⟩ :=
    b.exists_original_terminal_polygon_disk_with_clearance he hdim hi p hp hpi
      hfront hfull hint hends P hP hPi hdepth hencl s hA hU hC hUC hu hf hfi
      hS hF hPS hc hd hcd h0 h1 hinter
  have hUA : U ⊆ A := subset_union_left.trans hA.1
  have hCA : C ⊆ A := subset_union_right.trans hA.1
  have hfree : f '' U ∩ S ⊆ {f u0,f u1} := by
    rintro x ⟨⟨z,hz,rfl⟩,hxS⟩
    obtain ⟨w,hw,hh⟩ := hS.subset ⟨mem_image_of_mem f (hUA hz),hxS⟩
    have hwz := hfi (hCA hw) (hUA hz) hh
    have hzends := hUC.subset ⟨hz,hwz ▸ hw⟩
    simp only [mem_insert_iff,mem_singleton_iff] at hzends ⊢
    exact hzends.imp (congrArg f) (congrArg f)
  have hfullcontact : S ∩ frontier E = p '' (⋃ i, (Ps i).boundary ℝ) := by
    rw [hcontacts]
    ext x
    exact and_congr_right (fun hx => b.frontier_exterior_iff_interior he hdim hi (hSR hx))
  have hPdis (i : Fin m) (hik : i ≠ k) :
      Disjoint (p '' P.boundary ℝ) (p '' (Ps i).boundary ℝ) := by
    apply disjoint_left.mpr
    rintro x ⟨z,hz,rfl⟩ ⟨w,hw,hh⟩
    have hzAnn := mem_squareAnnulus_iff_depth.mpr
      ⟨(hdepth z hz).1.le,(hdepth z hz).2.le⟩
    have hwAnn := mem_squareAnnulus_iff_depth.mpr
      ⟨(hstrict i w hw).1.le,(hstrict i w hw).2.le⟩
    have hwz := hpi hwAnn hzAnn hh
    exact disjoint_left.mp (hdisjoint hik.symm) (hPk.symm.subset hz) (hwz ▸ hw)
  have hPsS (i : Fin m) : p '' (Ps i).boundary ℝ ⊆ S := by
    intro x hx
    exact (hcontacts.subset ((image_mono (subset_iUnion _ i)) hx)).1
  have finish (Z : Set P2) (hZ : IsFinitePLBallPair ℝ Z {c,d})
      (hZP : Z ⊆ P.boundary ℝ) (hrim : j '' sphere 0 1 = f '' U ∪ p '' Z) :
      j '' closedBall 0 1 ∩ S = p '' Z ∧
      f '' A ∩ j '' closedBall 0 1 = f '' U := by
    have hendsZ : {f u0,f u1} ⊆ p '' Z := by
      intro x hx
      rcases mem_insert_iff.mp hx with rfl | hx
      · exact ⟨c,hZ.1 (by simp),h0.symm⟩
      · rw [mem_singleton_iff] at hx
        subst x
        exact ⟨d,hZ.1 (by simp),h1.symm⟩
    have hrimS : j '' sphere 0 1 ∩ S = p '' Z := by
      rw [hrim]
      apply Subset.antisymm
      · rintro x ⟨hx,hxs⟩
        rcases hx with hx | hx
        · exact hendsZ (hfree ⟨hx,hxs⟩)
        · exact hx
      · intro x hx
        exact ⟨Or.inr hx,hPS ((image_mono hZP) hx)⟩
    have hother (i : Fin m) (hik : i ≠ k) :
        Disjoint (j '' closedBall 0 1) (p '' (Ps i).boundary ℝ) := by
      apply hclear (ns i) (Ps i) (hPs i).2 (hPs i).1 (hstrict i) (henclosing i)
      apply disjoint_left.mpr
      intro x hxr hxi
      exact disjoint_left.mp (hPdis i hik)
        ((image_mono hZP) (hrimS.subset ⟨hxr,hPsS i hxi⟩)) hxi
    constructor
    · apply Subset.antisymm
      · rintro x ⟨⟨z,hz,rfl⟩,hxS⟩
        by_cases hzr : z ∈ sphere (0 : Fin 2 → ℝ) 1
        · exact hrimS.subset ⟨mem_image_of_mem j hzr,hxS⟩
        have hxwhole := hfullcontact.subset ⟨hxS,hjF (mem_image_of_mem j hz)⟩
        obtain ⟨w,hw,hh⟩ := hxwhole
        obtain ⟨i,hiw⟩ := mem_iUnion.mp hw
        by_cases hik : i = k
        · subst i
          exact False.elim (disjoint_left.mp hjP ⟨z,⟨hz,hzr⟩,rfl⟩
            ⟨w,hPk.subset hiw,hh⟩)
        · exact False.elim (disjoint_left.mp (hother i hik)
            (mem_image_of_mem j hz) ⟨w,hiw,hh⟩)
      · intro x hx
        obtain ⟨z,hz,rfl⟩ := (hrimS.symm.subset hx).1
        exact ⟨mem_image_of_mem j (sphere_subset_closedBall hz),
          (hrimS.symm.subset hx).2⟩
    · apply Subset.antisymm
      · rintro x ⟨hxA,hxj⟩
        exact hF.subset ⟨hxA,hjF hxj⟩
      · intro x hxU
        have hxr : x ∈ j '' sphere 0 1 := hrim.symm.subset (Or.inl hxU)
        exact ⟨(image_mono hUA) hxU,(image_mono sphere_subset_closedBall) hxr⟩
  refine ⟨V,W,hV,hW,hVW,hVWint,?_⟩
  rcases hjr with hjr | hjr
  · exact ⟨V,Or.inl rfl,j,hj,hji,hjF,hjr,
      (finish V hV (fun z hz => hVW.subset (Or.inl hz)) hjr).1,
      (finish V hV (fun z hz => hVW.subset (Or.inl hz)) hjr).2⟩
  · exact ⟨W,Or.inr rfl,j,hj,hji,hjF,hjr,
      (finish W hW (fun z hz => hVW.subset (Or.inr hz)) hjr).1,
      (finish W hW (fun z hz => hVW.subset (Or.inr hz)) hjr).2⟩

end PoincareConjecture.M76
