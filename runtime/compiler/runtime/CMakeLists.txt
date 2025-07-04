################################################################################
# Copyright IBM Corp. and others 2017
#
# This program and the accompanying materials are made available under
# the terms of the Eclipse Public License 2.0 which accompanies this
# distribution and is available at https://www.eclipse.org/legal/epl-2.0/
# or the Apache License, Version 2.0 which accompanies this distribution and
# is available at https://www.apache.org/licenses/LICENSE-2.0.
#
# This Source Code may also be made available under the following
# Secondary Licenses when the conditions for such availability set
# forth in the Eclipse Public License, v. 2.0 are satisfied: GNU
# General Public License, version 2 with the GNU Classpath
# Exception [1] and GNU General Public License, version 2 with the
# OpenJDK Assembly Exception [2].
#
# [1] https://www.gnu.org/software/classpath/license.html
# [2] https://openjdk.org/legal/assembly-exception.html
#
# SPDX-License-Identifier: EPL-2.0 OR Apache-2.0 OR GPL-2.0-only WITH Classpath-exception-2.0 OR GPL-2.0-only WITH OpenJDK-assembly-exception-1.0
################################################################################

j9jit_files(
	runtime/ArtifactManager.cpp
	runtime/ClassUnloadAssumption.cpp
	runtime/codertinit.cpp
	runtime/CRuntimeImpl.cpp
	runtime/DataCache.cpp
	runtime/emfloat.c
	runtime/GPUHelpers.cpp
	runtime/HookHelpers.cpp
	runtime/HWProfiler.cpp
	runtime/IProfiler.cpp
	runtime/J9CodeCache.cpp
	runtime/J9CodeCacheManager.cpp
	runtime/J9CodeCacheMemorySegment.cpp
	runtime/J9JitPersistentMemory.cpp
	runtime/J9Profiler.cpp
	runtime/JitRuntime.cpp
	runtime/MetaData.cpp
	runtime/MetaDataDebug.cpp
	runtime/MethodMetaData.c
	runtime/RelocationRecord.cpp
	runtime/RelocationRuntime.cpp
	runtime/RelocationRuntimeLogger.cpp
	runtime/RelocationTarget.cpp
	runtime/RuntimeAssumptions.cpp
	runtime/Runtime.cpp
	runtime/SignalHandler.c
	runtime/SymbolValidationManager.cpp
	runtime/Trampoline.cpp
	runtime/ValueProfiler.cpp
)

# These files are added from OMR, because they're not part
# of the default list provided by create_omr_compiler_library
j9jit_files(
	${omr_SOURCE_DIR}/compiler/runtime/OMRRuntimeAssumptions.cpp
	${omr_SOURCE_DIR}/compiler/optimizer/PAG/PointerAssignmentGraph.cpp
	${omr_SOURCE_DIR}/compiler/optimizer/PAG/PAG_Components.cpp
	${omr_SOURCE_DIR}/compiler/optimizer/PAG/CallGraph.cpp
	${omr_SOURCE_DIR}/compiler/optimizer/PAG/regularPT.cpp
)


if(J9VM_OPT_JITSERVER)
	j9jit_files(
		runtime/CompileService.cpp
		runtime/JITClientSession.cpp
		runtime/JITServerAOTCache.cpp
		runtime/JITServerAOTDeserializer.cpp
		runtime/JITServerIProfiler.cpp
		runtime/JITServerProfileCache.cpp
		runtime/JITServerROMClassHash.cpp
		runtime/JITServerSharedROMClassCache.cpp
		runtime/JITServerStatisticsThread.cpp
		runtime/Listener.cpp
		runtime/MetricsServer.cpp
	)
endif()

if(J9VM_OPT_CRIU_SUPPORT)
	j9jit_files(
		runtime/CRRuntime.cpp
	)
endif()
