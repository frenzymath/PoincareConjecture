import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Coordinates.OriginalFaceAffineInverse
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.Systems.NormalFaceArcFamily
import PoincareConjecture.Proofs.M76.Mathlib.AffineIntrinsicFrontier
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallImages









set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)

theorem InCircleFreeNonreturningTriangleGraphPosition.exists_normal_arc_family_on_original_face
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E] [TopologicalSpace X]
    (K : SimplicialComplex ℝ E) (g : E → X) (hgi : InjOn g K.space)
    {s : Finset E} (hs : s ∈ K.faces)
    (Q : OpenPartialHomeomorph X V3) (A : E →ᴬ[ℝ] V3)
    (hmap : MapsTo g (convexHull ℝ (s : Set E)) Q.source)
    (hA : EqOn (Q ∘ g) A (convexHull ℝ (s : Set E)))
    {S : Set X} (hposition : InCircleFreeNonreturningTriangleGraphPosition Q S g s A) :
    ∃ (γ : Type) (_ : Finite γ) (d r : γ → Set E),
      (Pairwise fun i j => Disjoint (d i) (d j)) ∧
      g '' (⋃ i, d i) = S ∩ (g '' convexHull ℝ (s : Set E)) ∧
      (⋃ i, d i) ⊆ convexHull ℝ (s : Set E) ∧
      ∀ i, IsFinitePLBallPair ℝ (d i) (r i) ∧
        r i = d i ∩ intrinsicFrontier ℝ (convexHull ℝ (s : Set E)) ∧
        ∀ a : Finset E, a ⊆ s → a.card = 2 → ¬ r i ⊆ convexHull ℝ (a : Set E) := by
  classical
  obtain ⟨γ, hγ, d, r, hdis, hphysical, htarget, harcs⟩ :=
    hposition.exists_normal_arc_family K g hgi hs Q A hmap hA
  obtain ⟨B, hleft, hright, hBmap, hBphysical⟩ :=
    exists_original_face_chart_affine_inverse K g hgi hs Q A hmap hA
  let T := convexHull ℝ (A '' (s : Set E))
  let H := convexHull ℝ (s : Set E)
  have hBi : InjOn B T := hright.injOn
  have hdT (i) : d i ⊆ T := fun _ hx => (htarget (mem_iUnion.mpr ⟨i, hx⟩)).1
  have hnonempty : T.Nonempty := ((K.nonempty_of_mem_faces hs).to_set.image A).convexHull
  have hBspan : InjOn B (affineSpan ℝ T) :=
    B.toAffineMap.injOn_affineSpan_of_injOn_convex (convex_convexHull ℝ _) hnonempty hBi
  have hBH : B '' T = H := by
    refine Subset.antisymm hBmap.image_subset ?_
    intro x hx
    have hAx : A x ∈ T :=
      (A.toAffineMap.image_convexHull (s : Set E)).subset (mem_image_of_mem A hx)
    exact ⟨A x, hAx, hleft hx⟩
  have hfront : B '' intrinsicFrontier ℝ T = intrinsicFrontier ℝ H :=
    (B.toAffineMap.intrinsicFrontier_image_of_injOn T hBspan).symm.trans
      (congrArg (intrinsicFrontier ℝ) hBH)
  have hTclosed : IsClosed T :=
    ((s.finite_toSet.image A).isCompact_convexHull ℝ).isClosed
  have hgd (i) : g '' (B '' d i) = Q.symm '' d i := by
    rw [image_image]
    exact image_congr (fun x hx => hBphysical (hdT i hx))
  refine ⟨γ, hγ, fun i => B '' d i, fun i => B '' r i, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    apply disjoint_left.mpr
    rintro x ⟨y, hy, hyx⟩ ⟨z, hz, hzx⟩
    have heq : y = z := hBi (hdT i hy) (hdT j hz) (hyx.trans hzx.symm)
    exact disjoint_left.mp (hdis hij) hy (heq.symm ▸ hz)
  · rw [image_iUnion]
    simp_rw [hgd]
    rwa [image_iUnion] at hphysical
  · rintro x hx
    obtain ⟨i, y, hy, rfl⟩ := mem_iUnion.mp hx
    exact hBmap (hdT i hy)
  · intro i
    refine ⟨(harcs i).1.affine_image B (hBi.mono (hdT i)), ?_, ?_⟩
    · change B '' r i = (B '' d i) ∩ intrinsicFrontier ℝ H
      rw [(harcs i).2.1]
      apply Subset.antisymm
      · rintro x ⟨y, hy, rfl⟩
        exact ⟨mem_image_of_mem B hy.1, hfront.subset (mem_image_of_mem B hy.2)⟩
      · rintro x ⟨⟨y, hy, hyx⟩, hxfront⟩
        obtain ⟨z, hz, hzx⟩ := hfront.symm.subset hxfront
        have heq : y = z := hBi (hdT i hy) (intrinsicFrontier_subset hTclosed hz)
          (hyx.trans hzx.symm)
        exact ⟨y, ⟨hy, heq.symm ▸ hz⟩, hyx⟩
    · intro a has ha hsub
      apply (harcs i).2.2 a has ha
      intro y hy
      have hBy := hsub (mem_image_of_mem B hy)
      have hAy : A (B y) = y := hright (hdT i ((harcs i).1.1 hy))
      exact (A.toAffineMap.image_convexHull (a : Set E)).subset ⟨B y, hBy, hAy⟩

end PoincareConjecture.M76
