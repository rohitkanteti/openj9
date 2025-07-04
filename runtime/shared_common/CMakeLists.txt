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

omr_add_tracegen(j9shr.tdf)

j9vm_add_library(j9shrcommon STATIC
	AttachedDataManagerImpl.cpp
	ByteDataManagerImpl.cpp
	CacheLifecycleManager.cpp
	CacheMap.cpp
	ClassDebugDataProvider.cpp
	ClasspathItem.cpp
	ClasspathManagerImpl2.cpp
	CompiledMethodManagerImpl.cpp
	CompositeCache.cpp
	hookhelpers.cpp
	Manager.cpp
	Managers.cpp
	OSCache.cpp
	OSCacheFile.cpp
	OSCachemmap.cpp
	OSCachesysv.cpp
	ROMClassManagerImpl.cpp
	ROMClassResourceManager.cpp
	SCImplementedAPI.cpp
	ScopeManagerImpl.cpp
	shrinit.cpp
	TimestampManagerImpl.cpp
	${CMAKE_CURRENT_BINARY_DIR}/ut_j9shr.c
)
target_include_directories(j9shrcommon
	PRIVATE
		${j9vm_SOURCE_DIR}/shared
		${j9vm_SOURCE_DIR}/shared_util
		${j9vm_SOURCE_DIR}/verbose
	PUBLIC
		${CMAKE_CURRENT_BINARY_DIR}
		include
		.
)
target_link_libraries(j9shrcommon
	PRIVATE
		j9vm_interface
		j9pool
		j9hashtable
		j9utilcore
		j9util
		j9jit
)

target_enable_ddr(j9shrcommon GLOB_HEADERS)
ddr_set_add_targets(j9ddr j9shrcommon)
