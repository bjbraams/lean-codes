/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import ComplexAnalysis.UnivalentDisk.Geometry
public import ComplexAnalysis.UnivalentDisk.Separation
public import ComplexAnalysis.UnivalentDisk.Index
public import ComplexAnalysis.UnivalentDisk.CauchyFormula
public import ComplexAnalysis.UnivalentDisk.Exhaustion

/-!
# Jordan contours constructed from injective holomorphic disk maps

The image of a circle under a map injective and holomorphic on a larger disk is a simple
smooth contour. Its complement has precisely two connected components: the image disk
and the exterior of the image closed disk. Its index is one in the interior and zero
in the exterior, and the Banach-valued Cauchy formula holds with the usual normalization.
The disk image is simply connected.

Smaller concentric image disks form a relatively compact exhaustion of a univalent disk
image, with nested closures and eventual containment of every compact subset. Holomorphy
on the limiting boundary is not required.

The injective holomorphic parametrization is an explicit hypothesis. This library does
not yet construct such a parametrization for an arbitrary simply connected proper planar
domain, nor prove the Jordan curve theorem for arbitrary embedded circles.
-/
