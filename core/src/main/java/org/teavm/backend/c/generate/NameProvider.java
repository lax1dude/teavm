/*
 *  Copyright 2018 Alexey Andreev.
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *       http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 */
package org.teavm.backend.c.generate;

import java.util.Arrays;
import java.util.Collections;
import java.util.HashSet;
import java.util.Set;
import org.teavm.backend.lowlevel.generate.LowLevelNameProvider;
import org.teavm.model.ClassReaderSource;
import org.teavm.model.FieldReference;
import org.teavm.runtime.RuntimeArray;
import org.teavm.runtime.RuntimeClass;
import org.teavm.runtime.RuntimeObject;

public class NameProvider extends LowLevelNameProvider {
    private static final Set<? extends String> keywords = Collections.unmodifiableSet(new HashSet<>(Arrays.asList(
            "auto", "break", "case", "char", "const", "continue", "default", "do", "double", "else",
            "enum", "extern", "float", "for", "goto", "if", "inline", "int", "long", "register", "restrict",
            "return", "short", "signed", "sizeof", "static", "struct", "switch", "typedef", "union",
            "unsigned", "void", "volatile", "while"
    )));

    public NameProvider(ClassReaderSource classSource) {
        super(classSource);

        occupiedTopLevelNames.add("TeaVM_Object");
        occupiedTopLevelNames.add("TeaVM_Array");
        occupiedTopLevelNames.add("TeaVM_String");
        occupiedTopLevelNames.add("TeaVM_Class");

        classNames.put(RuntimeObject.class.getName(), "TeaVM_Object");
        classNames.put(Object.class.getName(), "TeaVM_Object");
        classNames.put(String.class.getName(), "TeaVM_String");
        classNames.put(RuntimeClass.class.getName(), "TeaVM_Class");
        classNames.put(RuntimeArray.class.getName(), "TeaVM_Array");

        memberFieldNames.put(new FieldReference(RuntimeObject.class.getName(), "classReference"), "header");
        memberFieldNames.put(new FieldReference(RuntimeObject.class.getName(), "hashCode"), "hash");
        memberFieldNames.put(new FieldReference(RuntimeArray.class.getName(), "size"), "size");
        memberFieldNames.put(new FieldReference(String.class.getName(), "characters"), "characters");
        memberFieldNames.put(new FieldReference(String.class.getName(), "hashCode"), "hashCode");

        for (String name : new String[] { "size", "flags", "tag", "canary", "name", "itemType", "arrayType",
                "isSupertypeOf", "init", "enumValues", "layout", "simpleName" }) {
            memberFieldNames.put(new FieldReference(RuntimeClass.class.getName(), name), name);
        }
        memberFieldNames.put(new FieldReference(RuntimeClass.class.getName(), "parent"), "superclass");

        occupiedClassNames.put(RuntimeObject.class.getName(), new HashSet<>(Arrays.asList("header")));
        occupiedClassNames.put(RuntimeArray.class.getName(), new HashSet<>(Arrays.asList("length")));
    }

    @Override
    protected Set<? extends String> getKeywords() {
        return keywords;
    }
}
