import PoincareLib.Topology.Manifold.Smoothing.PrimeReduction.Reattachment.CocoreCircleTube
import PoincareLib.Topology.Manifold.Smoothing.PrimeReduction.Disks.SeparatedTubeCaps
import PoincareLib.Topology.Manifold.Smoothing.PrimeReduction.Collars.CircleNormalSides

/-! # Separated off-level caps from the actual cocore tube

The constructed tube determines both raw caps and their common planar core.
A supported signed displacement separates the caps, fixes their full rims,
and removes every new cap point from the selected cocore level.
-/

set_option autoImplicit false
open Set Geometry Metric

namespace PoincareMT.M76
open PoincareMT.M76.Dehn
local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "P3" => ((ℝ × ℝ) × ℝ)

theorem ChartwisePLSphere.exists_cocore_separated_caps
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {S : Set X}
    (s : ChartwisePLSphere e S) (Q : OpenPartialHomeomorph X V3)
    (hQ : ∀ i, (e i).symm.trans Q ∈ piecewiseAffineGroupoid V3)
    (J : SimplicialComplex ℝ V3) (hJ : J.faces.Finite) (hJQ : J.space ⊆ Q.target)
    (hJcv : Convex ℝ J.space)
    (H : V3 ≃ᴬ[ℝ] P3) {a b : ℝ} (hab : a < b)
    (hband : ∀ x ∈ Q '' (S ∩ Q.source) ∩ J.space,
      (H x).2 ∈ Ioo a b → x ∈ interior J.space) :
    ∃ t ∈ Ioo a b,
      ((Q '' (S ∩ Q.source) ∩ J.space) ∩ {x | (H x).2 = t} = ∅) ∨
      ∃ (n : ℕ) (L : Polygon V3 (n + 3)) (D U : Set V3) (k : ℕ) (sigma : P3 → V3)
        (caps : Bool → Set V3),
        Function.Injective L ∧ L.HasSimplicialEdges ∧
        IsFinitePLBallPair P2 D (L.boundary ℝ) ∧
        D ⊆ interior J.space ∩ {x | (H x).2 = t} ∧
        D ∩ Q '' (S ∩ Q.source) = L.boundary ℝ ∧
        IsOpen U ∧ D ⊆ U ∧ U ⊆ interior J.space ∧
        (∀ x ∈ U, x ∈ L.boundary ℝ ↔ Q.symm x ∈ S ∧ (H x).2 = t) ∧
        FinitePiecewiseAffineOn sigma (signedTubeDiamond ×ˢ Icc (0 : ℝ) (k+3)) ∧
        MapsTo sigma (signedTubeDiamond ×ˢ Icc (0 : ℝ) (k+3)) U ∧
        L.boundary ℝ ⊆ interior (sigma '' (signedTubeDiamond ×ˢ Icc (0 : ℝ) (k+3))) ∧
        (∀ x ∈ signedTubeDiamond ×ˢ Icc (0 : ℝ) (k+3),
          (H (sigma x)).2 = t ↔ x.1 ∈ signedTubeSheet 0) ∧
        (∀ x ∈ signedTubeDiamond ×ˢ Icc (0 : ℝ) (k+3),
          Q.symm (sigma x) ∈ S ↔ x.1 ∈ signedTubeSheet 1) ∧
        (∀ x ∈ signedTubeDiamond ×ˢ Icc (0 : ℝ) (k+3),
          sigma x ∈ L.boundary ℝ ↔ x.1 = (0,0)) ∧
        (fun u : ℝ => sigma ((0,0),u)) '' Icc (0 : ℝ) (k+3) = L.boundary ℝ ∧
        (∀ x ∈ signedTubeDiamond ×ˢ Icc (0 : ℝ) (k+3),
          ∀ y ∈ signedTubeDiamond ×ˢ Icc (0 : ℝ) (k+3),
          sigma x = sigma y ↔ x.1 = y.1 ∧
            (x.2 = y.2 ∨ (x.2 = 0 ∧ y.2 = k+3) ∨ (y.2 = 0 ∧ x.2 = k+3))) ∧
        (∀ b, IsFinitePLBallPair P2 (caps b)
            ((fun u => sigma ((if b then 1/4 else -1/4,0),u)) '' Icc (0 : ℝ) (k+3)) ∧
          caps b ⊆ U ∧
          caps b ∩ Q '' (S ∩ Q.source) =
            (fun u => sigma ((if b then 1/4 else -1/4,0),u)) '' Icc (0 : ℝ) (k+3) ∧
          Disjoint (caps b) {x | (H x).2 = t}) ∧
        Disjoint (caps true) (caps false) := by
  obtain ⟨t,ht,hempty | ⟨n,L,D,U,k,sigma,hLi,hL,hD,hDsub,hcontact,hU,hDU,hUJ,
      hisolate,hSigma,hMap,hInt,hPlane,hSphere,hAxis,hImage,hFib⟩⟩ :=
    s.exists_cocore_innermost_circle_tube Q hQ J hJ hJQ hJcv H hab hband
  · exact ⟨t,ht,Or.inl hempty⟩
  · obtain ⟨M,hM,hMs,_,hMlocal⟩ := s.exists_finite_chart_carrier Q hQ J hJ hJQ
    let A : V3 →ᴬ[ℝ] ℝ :=
      (ContinuousLinearMap.snd ℝ P2 ℝ).toContinuousAffineMap.comp H.toContinuousAffineMap -
        ContinuousAffineMap.const ℝ V3 t
    have hAx (x : V3) : A x = (H x).2 - t := rfl
    have hA : A.linear ≠ 0 := by
      intro hzero
      obtain ⟨c,hc⟩ := A.toAffineMap.linear_eq_zero_iff_exists_const.mp hzero
      have h0 := DFunLike.congr_fun hc (H.symm ((0,0),0))
      have h1 := DFunLike.congr_fun hc (H.symm ((0,0),1))
      change A (H.symm ((0,0),0)) = c at h0
      change A (H.symm ((0,0),1)) = c at h1
      rw [hAx,H.apply_symm_apply] at h0 h1
      norm_num at h0 h1
      linarith
    have hzero : ∀ x ∈ signedTubeDiamond ×ˢ Icc (0 : ℝ) (k+3),
        A (sigma x) = 0 ↔ x.1.1 = 0 := by
      intro x hx
      rw [hAx,sub_eq_zero,hPlane x hx,signedTubeSheet_coordinate_iff _ hx.1]
      simp
    have haxis0 : sigma ((0,0),0) ∈ L.boundary ℝ :=
      hImage.subset ⟨0,⟨le_rfl,by positivity⟩,rfl⟩
    have hsides := circle_tube_affine_height_sides (by positivity : (0 : ℝ) ≤ k+3)
      sigma hSigma.continuousOn A hA hzero (hInt haxis0)
    let F : P2 →ᴬ[ℝ] V3 := H.symm.toContinuousAffineMap.comp
      ((ContinuousAffineMap.id ℝ P2).prod (ContinuousAffineMap.const ℝ P2 t))
    let G : V3 →ᴬ[ℝ] P2 :=
      (ContinuousLinearMap.fst ℝ P2 ℝ).toContinuousAffineMap.comp H.toContinuousAffineMap
    have hF (z : P2) : F z = H.symm (z,t) := rfl
    have hG (x : V3) : G x = (H x).1 := rfl
    have hleft : Function.LeftInverse G F := by
      intro z
      rw [hG,hF,H.apply_symm_apply]
    have hright : EqOn (F ∘ G) id {x | (H x).2 = t} := by
      intro x hx
      change F (G x) = x
      rw [hF,hG,← hx]
      exact H.symm_apply_apply x
    have hDM : D ∩ M.space = L.boundary ℝ := by
      apply Subset.antisymm
      · intro x hx
        exact hcontact.subset ⟨hx.1,(hMs.subset hx.2).1⟩
      · intro x hx
        refine ⟨hD.1 hx,?_⟩
        rw [hMs]
        exact ⟨(hcontact.symm.subset hx).2,interior_subset (hDsub (hD.1 hx)).1⟩
    have hSphereM : ∀ x ∈ signedTubeDiamond ×ˢ Icc (0 : ℝ) (k+3),
        sigma x ∈ M.space ↔ x.1 ∈ signedTubeSheet 1 := by
      intro x hx
      exact (hMlocal _ (interior_subset (hUJ (hMap hx)))).symm.trans (hSphere x hx)
    obtain ⟨caps,hcaps,hdis⟩ := exists_separated_caps_of_circle_tube L hL hLi hD
      (fun x hx => (hDsub hx).2) F G hleft hright M hM hDM hU hDU
      (by positivity : (0 : ℝ) < k+3) sigma hSigma hMap hPlane hSphereM hAxis hFib
      A.toAffineMap hA (fun x hx => sub_eq_zero.mpr hx) hzero hsides
    refine ⟨t,ht,Or.inr ⟨n,L,D,U,k,sigma,caps,hLi,hL,hD,hDsub,hcontact,hU,hDU,hUJ,
      hisolate,hSigma,hMap,hInt,hPlane,hSphere,hAxis,hImage,hFib,?_,hdis⟩⟩
    intro b
    refine ⟨(hcaps b).1,(hcaps b).2.1,?_,(hcaps b).2.2.2⟩
    rw [← (hcaps b).2.2.1]
    ext x
    constructor
    · rintro ⟨hx,hxS⟩
      exact ⟨hx,hMs.symm.subset ⟨hxS,interior_subset (hUJ ((hcaps b).2.1 hx))⟩⟩
    · rintro ⟨hx,hxM⟩
      exact ⟨hx,(hMs.subset hxM).1⟩

end PoincareMT.M76
