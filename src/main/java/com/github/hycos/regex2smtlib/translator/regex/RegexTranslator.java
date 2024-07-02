/**
 * regex2smtlib: A regex to smtlib translator
 *
 * The MIT License (MIT)
 *
 * Copyright (c) 2017 Julian Thome <julian.thome.de@gmail.com>
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of
 * this software and associated documentation files (the "Software"), to deal in
 * the Software without restriction, including without limitation the rights to
 * use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies
 * of the Software, and to permit persons to whom the Software is furnished to do
 * so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
 * SOFTWARE.
 **/

package com.github.hycos.regex2smtlib.translator.regex;

import com.github.hycos.regex2smtlib.translator.TranslationMap;
import com.github.hycos.regex2smtlib.regexparser.RegexParser;
import org.apache.commons.lang3.StringUtils;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import org.snt.inmemantlr.exceptions.IllegalWorkflowException;
import org.snt.inmemantlr.exceptions.ParseTreeProcessorException;
import org.snt.inmemantlr.exceptions.ParsingException;
import org.snt.inmemantlr.tree.ParseTreeNode;

import java.util.regex.Matcher;
import java.util.regex.Pattern;

import static com.github.hycos.regex2smtlib.translator.TranslationMap.Element.*;


public class RegexTranslator extends AbstractRegexTranslator {

    final static Logger LOGGER = LoggerFactory.getLogger(RegexTranslator.class);


    private TranslationMap tmap;
    private EscapingFunction escaper;

    private static String wordChars = "(re.union (re.range \"\\u{30}\" \"\\u{39}\") (re.range \"\\u{41}\" \"\\u{5a}\") (re.range \"\\u{5f}\" \"\\u{5f}\") (re.range \"\\u{61}\" \"\\u{7a}\") (re.range \"\\u{aa}\" \"\\u{aa}\") (re.range \"\\u{b5}\" \"\\u{b5}\") (re.range \"\\u{ba}\" \"\\u{ba}\") (re.range \"\\u{c0}\" \"\\u{d6}\") (re.range \"\\u{d8}\" \"\\u{f6}\") (re.range \"\\u{f8}\" \"\\u{2c1}\") (re.range \"\\u{2c6}\" \"\\u{2d1}\") (re.range \"\\u{2e0}\" \"\\u{2e4}\") (re.range \"\\u{2ec}\" \"\\u{2ec}\") (re.range \"\\u{2ee}\" \"\\u{2ee}\") (re.range \"\\u{300}\" \"\\u{374}\") (re.range \"\\u{376}\" \"\\u{377}\") (re.range \"\\u{37a}\" \"\\u{37d}\") (re.range \"\\u{37f}\" \"\\u{37f}\") (re.range \"\\u{386}\" \"\\u{386}\") (re.range \"\\u{388}\" \"\\u{38a}\") (re.range \"\\u{38c}\" \"\\u{38c}\") (re.range \"\\u{38e}\" \"\\u{3a1}\") (re.range \"\\u{3a3}\" \"\\u{3f5}\") (re.range \"\\u{3f7}\" \"\\u{481}\") (re.range \"\\u{483}\" \"\\u{52f}\") (re.range \"\\u{531}\" \"\\u{556}\") (re.range \"\\u{559}\" \"\\u{559}\") (re.range \"\\u{561}\" \"\\u{587}\") (re.range \"\\u{591}\" \"\\u{5bd}\") (re.range \"\\u{5bf}\" \"\\u{5bf}\") (re.range \"\\u{5c1}\" \"\\u{5c2}\") (re.range \"\\u{5c4}\" \"\\u{5c5}\") (re.range \"\\u{5c7}\" \"\\u{5c7}\") (re.range \"\\u{5d0}\" \"\\u{5ea}\") (re.range \"\\u{5f0}\" \"\\u{5f2}\") (re.range \"\\u{610}\" \"\\u{61a}\") (re.range \"\\u{620}\" \"\\u{669}\") (re.range \"\\u{66e}\" \"\\u{6d3}\") (re.range \"\\u{6d5}\" \"\\u{6dc}\") (re.range \"\\u{6df}\" \"\\u{6e8}\") (re.range \"\\u{6ea}\" \"\\u{6fc}\") (re.range \"\\u{6ff}\" \"\\u{6ff}\") (re.range \"\\u{710}\" \"\\u{74a}\") (re.range \"\\u{74d}\" \"\\u{7b1}\") (re.range \"\\u{7c0}\" \"\\u{7f5}\") (re.range \"\\u{7fa}\" \"\\u{7fa}\") (re.range \"\\u{800}\" \"\\u{82d}\") (re.range \"\\u{840}\" \"\\u{85b}\") (re.range \"\\u{860}\" \"\\u{86a}\") (re.range \"\\u{8a0}\" \"\\u{8b4}\") (re.range \"\\u{8b6}\" \"\\u{8bd}\") (re.range \"\\u{8d4}\" \"\\u{8e1}\") (re.range \"\\u{8e3}\" \"\\u{963}\") (re.range \"\\u{966}\" \"\\u{96f}\") (re.range \"\\u{971}\" \"\\u{983}\") (re.range \"\\u{985}\" \"\\u{98c}\") (re.range \"\\u{98f}\" \"\\u{990}\") (re.range \"\\u{993}\" \"\\u{9a8}\") (re.range \"\\u{9aa}\" \"\\u{9b0}\") (re.range \"\\u{9b2}\" \"\\u{9b2}\") (re.range \"\\u{9b6}\" \"\\u{9b9}\") (re.range \"\\u{9bc}\" \"\\u{9c4}\") (re.range \"\\u{9c7}\" \"\\u{9c8}\") (re.range \"\\u{9cb}\" \"\\u{9ce}\") (re.range \"\\u{9d7}\" \"\\u{9d7}\") (re.range \"\\u{9dc}\" \"\\u{9dd}\") (re.range \"\\u{9df}\" \"\\u{9e3}\") (re.range \"\\u{9e6}\" \"\\u{9f1}\") (re.range \"\\u{9fc}\" \"\\u{9fc}\") (re.range \"\\u{a01}\" \"\\u{a03}\") (re.range \"\\u{a05}\" \"\\u{a0a}\") (re.range \"\\u{a0f}\" \"\\u{a10}\") (re.range \"\\u{a13}\" \"\\u{a28}\") (re.range \"\\u{a2a}\" \"\\u{a30}\") (re.range \"\\u{a32}\" \"\\u{a33}\") (re.range \"\\u{a35}\" \"\\u{a36}\") (re.range \"\\u{a38}\" \"\\u{a39}\") (re.range \"\\u{a3c}\" \"\\u{a3c}\") (re.range \"\\u{a3e}\" \"\\u{a42}\") (re.range \"\\u{a47}\" \"\\u{a48}\") (re.range \"\\u{a4b}\" \"\\u{a4d}\") (re.range \"\\u{a51}\" \"\\u{a51}\") (re.range \"\\u{a59}\" \"\\u{a5c}\") (re.range \"\\u{a5e}\" \"\\u{a5e}\") (re.range \"\\u{a66}\" \"\\u{a75}\") (re.range \"\\u{a81}\" \"\\u{a83}\") (re.range \"\\u{a85}\" \"\\u{a8d}\") (re.range \"\\u{a8f}\" \"\\u{a91}\") (re.range \"\\u{a93}\" \"\\u{aa8}\") (re.range \"\\u{aaa}\" \"\\u{ab0}\") (re.range \"\\u{ab2}\" \"\\u{ab3}\") (re.range \"\\u{ab5}\" \"\\u{ab9}\") (re.range \"\\u{abc}\" \"\\u{ac5}\") (re.range \"\\u{ac7}\" \"\\u{ac9}\") (re.range \"\\u{acb}\" \"\\u{acd}\") (re.range \"\\u{ad0}\" \"\\u{ad0}\") (re.range \"\\u{ae0}\" \"\\u{ae3}\") (re.range \"\\u{ae6}\" \"\\u{aef}\") (re.range \"\\u{af9}\" \"\\u{aff}\") (re.range \"\\u{b01}\" \"\\u{b03}\") (re.range \"\\u{b05}\" \"\\u{b0c}\") (re.range \"\\u{b0f}\" \"\\u{b10}\") (re.range \"\\u{b13}\" \"\\u{b28}\") (re.range \"\\u{b2a}\" \"\\u{b30}\") (re.range \"\\u{b32}\" \"\\u{b33}\") (re.range \"\\u{b35}\" \"\\u{b39}\") (re.range \"\\u{b3c}\" \"\\u{b44}\") (re.range \"\\u{b47}\" \"\\u{b48}\") (re.range \"\\u{b4b}\" \"\\u{b4d}\") (re.range \"\\u{b56}\" \"\\u{b57}\") (re.range \"\\u{b5c}\" \"\\u{b5d}\") (re.range \"\\u{b5f}\" \"\\u{b63}\") (re.range \"\\u{b66}\" \"\\u{b6f}\") (re.range \"\\u{b71}\" \"\\u{b71}\") (re.range \"\\u{b82}\" \"\\u{b83}\") (re.range \"\\u{b85}\" \"\\u{b8a}\") (re.range \"\\u{b8e}\" \"\\u{b90}\") (re.range \"\\u{b92}\" \"\\u{b95}\") (re.range \"\\u{b99}\" \"\\u{b9a}\") (re.range \"\\u{b9c}\" \"\\u{b9c}\") (re.range \"\\u{b9e}\" \"\\u{b9f}\") (re.range \"\\u{ba3}\" \"\\u{ba4}\") (re.range \"\\u{ba8}\" \"\\u{baa}\") (re.range \"\\u{bae}\" \"\\u{bb9}\") (re.range \"\\u{bbe}\" \"\\u{bc2}\") (re.range \"\\u{bc6}\" \"\\u{bc8}\") (re.range \"\\u{bca}\" \"\\u{bcd}\") (re.range \"\\u{bd0}\" \"\\u{bd0}\") (re.range \"\\u{bd7}\" \"\\u{bd7}\") (re.range \"\\u{be6}\" \"\\u{bef}\") (re.range \"\\u{c00}\" \"\\u{c03}\") (re.range \"\\u{c05}\" \"\\u{c0c}\") (re.range \"\\u{c0e}\" \"\\u{c10}\") (re.range \"\\u{c12}\" \"\\u{c28}\") (re.range \"\\u{c2a}\" \"\\u{c39}\") (re.range \"\\u{c3d}\" \"\\u{c44}\") (re.range \"\\u{c46}\" \"\\u{c48}\") (re.range \"\\u{c4a}\" \"\\u{c4d}\") (re.range \"\\u{c55}\" \"\\u{c56}\") (re.range \"\\u{c58}\" \"\\u{c5a}\") (re.range \"\\u{c60}\" \"\\u{c63}\") (re.range \"\\u{c66}\" \"\\u{c6f}\") (re.range \"\\u{c80}\" \"\\u{c83}\") (re.range \"\\u{c85}\" \"\\u{c8c}\") (re.range \"\\u{c8e}\" \"\\u{c90}\") (re.range \"\\u{c92}\" \"\\u{ca8}\") (re.range \"\\u{caa}\" \"\\u{cb3}\") (re.range \"\\u{cb5}\" \"\\u{cb9}\") (re.range \"\\u{cbc}\" \"\\u{cc4}\") (re.range \"\\u{cc6}\" \"\\u{cc8}\") (re.range \"\\u{cca}\" \"\\u{ccd}\") (re.range \"\\u{cd5}\" \"\\u{cd6}\") (re.range \"\\u{cde}\" \"\\u{cde}\") (re.range \"\\u{ce0}\" \"\\u{ce3}\") (re.range \"\\u{ce6}\" \"\\u{cef}\") (re.range \"\\u{cf1}\" \"\\u{cf2}\") (re.range \"\\u{d00}\" \"\\u{d03}\") (re.range \"\\u{d05}\" \"\\u{d0c}\") (re.range \"\\u{d0e}\" \"\\u{d10}\") (re.range \"\\u{d12}\" \"\\u{d44}\") (re.range \"\\u{d46}\" \"\\u{d48}\") (re.range \"\\u{d4a}\" \"\\u{d4e}\") (re.range \"\\u{d54}\" \"\\u{d57}\") (re.range \"\\u{d5f}\" \"\\u{d63}\") (re.range \"\\u{d66}\" \"\\u{d6f}\") (re.range \"\\u{d7a}\" \"\\u{d7f}\") (re.range \"\\u{d82}\" \"\\u{d83}\") (re.range \"\\u{d85}\" \"\\u{d96}\") (re.range \"\\u{d9a}\" \"\\u{db1}\") (re.range \"\\u{db3}\" \"\\u{dbb}\") (re.range \"\\u{dbd}\" \"\\u{dbd}\") (re.range \"\\u{dc0}\" \"\\u{dc6}\") (re.range \"\\u{dca}\" \"\\u{dca}\") (re.range \"\\u{dcf}\" \"\\u{dd4}\") (re.range \"\\u{dd6}\" \"\\u{dd6}\") (re.range \"\\u{dd8}\" \"\\u{ddf}\") (re.range \"\\u{de6}\" \"\\u{def}\") (re.range \"\\u{df2}\" \"\\u{df3}\") (re.range \"\\u{e01}\" \"\\u{e3a}\") (re.range \"\\u{e40}\" \"\\u{e4e}\") (re.range \"\\u{e50}\" \"\\u{e59}\") (re.range \"\\u{e81}\" \"\\u{e82}\") (re.range \"\\u{e84}\" \"\\u{e84}\") (re.range \"\\u{e87}\" \"\\u{e88}\") (re.range \"\\u{e8a}\" \"\\u{e8a}\") (re.range \"\\u{e8d}\" \"\\u{e8d}\") (re.range \"\\u{e94}\" \"\\u{e97}\") (re.range \"\\u{e99}\" \"\\u{e9f}\") (re.range \"\\u{ea1}\" \"\\u{ea3}\") (re.range \"\\u{ea5}\" \"\\u{ea5}\") (re.range \"\\u{ea7}\" \"\\u{ea7}\") (re.range \"\\u{eaa}\" \"\\u{eab}\") (re.range \"\\u{ead}\" \"\\u{eb9}\") (re.range \"\\u{ebb}\" \"\\u{ebd}\") (re.range \"\\u{ec0}\" \"\\u{ec4}\") (re.range \"\\u{ec6}\" \"\\u{ec6}\") (re.range \"\\u{ec8}\" \"\\u{ecd}\") (re.range \"\\u{ed0}\" \"\\u{ed9}\") (re.range \"\\u{edc}\" \"\\u{edf}\") (re.range \"\\u{f00}\" \"\\u{f00}\") (re.range \"\\u{f18}\" \"\\u{f19}\") (re.range \"\\u{f20}\" \"\\u{f29}\") (re.range \"\\u{f35}\" \"\\u{f35}\") (re.range \"\\u{f37}\" \"\\u{f37}\") (re.range \"\\u{f39}\" \"\\u{f39}\") (re.range \"\\u{f3e}\" \"\\u{f47}\") (re.range \"\\u{f49}\" \"\\u{f6c}\") (re.range \"\\u{f71}\" \"\\u{f84}\") (re.range \"\\u{f86}\" \"\\u{f97}\") (re.range \"\\u{f99}\" \"\\u{fbc}\") (re.range \"\\u{fc6}\" \"\\u{fc6}\") (re.range \"\\u{1000}\" \"\\u{1049}\") (re.range \"\\u{1050}\" \"\\u{109d}\") (re.range \"\\u{10a0}\" \"\\u{10c5}\") (re.range \"\\u{10c7}\" \"\\u{10c7}\") (re.range \"\\u{10cd}\" \"\\u{10cd}\") (re.range \"\\u{10d0}\" \"\\u{10fa}\") (re.range \"\\u{10fc}\" \"\\u{1248}\") (re.range \"\\u{124a}\" \"\\u{124d}\") (re.range \"\\u{1250}\" \"\\u{1256}\") (re.range \"\\u{1258}\" \"\\u{1258}\") (re.range \"\\u{125a}\" \"\\u{125d}\") (re.range \"\\u{1260}\" \"\\u{1288}\") (re.range \"\\u{128a}\" \"\\u{128d}\") (re.range \"\\u{1290}\" \"\\u{12b0}\") (re.range \"\\u{12b2}\" \"\\u{12b5}\") (re.range \"\\u{12b8}\" \"\\u{12be}\") (re.range \"\\u{12c0}\" \"\\u{12c0}\") (re.range \"\\u{12c2}\" \"\\u{12c5}\") (re.range \"\\u{12c8}\" \"\\u{12d6}\") (re.range \"\\u{12d8}\" \"\\u{1310}\") (re.range \"\\u{1312}\" \"\\u{1315}\") (re.range \"\\u{1318}\" \"\\u{135a}\") (re.range \"\\u{135d}\" \"\\u{135f}\") (re.range \"\\u{1380}\" \"\\u{138f}\") (re.range \"\\u{13a0}\" \"\\u{13f5}\") (re.range \"\\u{13f8}\" \"\\u{13fd}\") (re.range \"\\u{1401}\" \"\\u{166c}\") (re.range \"\\u{166f}\" \"\\u{167f}\") (re.range \"\\u{1681}\" \"\\u{169a}\") (re.range \"\\u{16a0}\" \"\\u{16ea}\") (re.range \"\\u{16ee}\" \"\\u{16f8}\") (re.range \"\\u{1700}\" \"\\u{170c}\") (re.range \"\\u{170e}\" \"\\u{1714}\") (re.range \"\\u{1720}\" \"\\u{1734}\") (re.range \"\\u{1740}\" \"\\u{1753}\") (re.range \"\\u{1760}\" \"\\u{176c}\") (re.range \"\\u{176e}\" \"\\u{1770}\") (re.range \"\\u{1772}\" \"\\u{1773}\") (re.range \"\\u{1780}\" \"\\u{17d3}\") (re.range \"\\u{17d7}\" \"\\u{17d7}\") (re.range \"\\u{17dc}\" \"\\u{17dd}\") (re.range \"\\u{17e0}\" \"\\u{17e9}\") (re.range \"\\u{180b}\" \"\\u{180d}\") (re.range \"\\u{1810}\" \"\\u{1819}\") (re.range \"\\u{1820}\" \"\\u{1877}\") (re.range \"\\u{1880}\" \"\\u{18aa}\") (re.range \"\\u{18b0}\" \"\\u{18f5}\") (re.range \"\\u{1900}\" \"\\u{191e}\") (re.range \"\\u{1920}\" \"\\u{192b}\") (re.range \"\\u{1930}\" \"\\u{193b}\") (re.range \"\\u{1946}\" \"\\u{196d}\") (re.range \"\\u{1970}\" \"\\u{1974}\") (re.range \"\\u{1980}\" \"\\u{19ab}\") (re.range \"\\u{19b0}\" \"\\u{19c9}\") (re.range \"\\u{19d0}\" \"\\u{19d9}\") (re.range \"\\u{1a00}\" \"\\u{1a1b}\") (re.range \"\\u{1a20}\" \"\\u{1a5e}\") (re.range \"\\u{1a60}\" \"\\u{1a7c}\") (re.range \"\\u{1a7f}\" \"\\u{1a89}\") (re.range \"\\u{1a90}\" \"\\u{1a99}\") (re.range \"\\u{1aa7}\" \"\\u{1aa7}\") (re.range \"\\u{1ab0}\" \"\\u{1abe}\") (re.range \"\\u{1b00}\" \"\\u{1b4b}\") (re.range \"\\u{1b50}\" \"\\u{1b59}\") (re.range \"\\u{1b6b}\" \"\\u{1b73}\") (re.range \"\\u{1b80}\" \"\\u{1bf3}\") (re.range \"\\u{1c00}\" \"\\u{1c37}\") (re.range \"\\u{1c40}\" \"\\u{1c49}\") (re.range \"\\u{1c4d}\" \"\\u{1c7d}\") (re.range \"\\u{1c80}\" \"\\u{1c88}\") (re.range \"\\u{1cd0}\" \"\\u{1cd2}\") (re.range \"\\u{1cd4}\" \"\\u{1cf9}\") (re.range \"\\u{1d00}\" \"\\u{1df9}\") (re.range \"\\u{1dfb}\" \"\\u{1f15}\") (re.range \"\\u{1f18}\" \"\\u{1f1d}\") (re.range \"\\u{1f20}\" \"\\u{1f45}\") (re.range \"\\u{1f48}\" \"\\u{1f4d}\") (re.range \"\\u{1f50}\" \"\\u{1f57}\") (re.range \"\\u{1f59}\" \"\\u{1f59}\") (re.range \"\\u{1f5b}\" \"\\u{1f5b}\") (re.range \"\\u{1f5d}\" \"\\u{1f5d}\") (re.range \"\\u{1f5f}\" \"\\u{1f7d}\") (re.range \"\\u{1f80}\" \"\\u{1fb4}\") (re.range \"\\u{1fb6}\" \"\\u{1fbc}\") (re.range \"\\u{1fbe}\" \"\\u{1fbe}\") (re.range \"\\u{1fc2}\" \"\\u{1fc4}\") (re.range \"\\u{1fc6}\" \"\\u{1fcc}\") (re.range \"\\u{1fd0}\" \"\\u{1fd3}\") (re.range \"\\u{1fd6}\" \"\\u{1fdb}\") (re.range \"\\u{1fe0}\" \"\\u{1fec}\") (re.range \"\\u{1ff2}\" \"\\u{1ff4}\") (re.range \"\\u{1ff6}\" \"\\u{1ffc}\") (re.range \"\\u{200c}\" \"\\u{200d}\") (re.range \"\\u{203f}\" \"\\u{2040}\") (re.range \"\\u{2054}\" \"\\u{2054}\") (re.range \"\\u{2071}\" \"\\u{2071}\") (re.range \"\\u{207f}\" \"\\u{207f}\") (re.range \"\\u{2090}\" \"\\u{209c}\") (re.range \"\\u{20d0}\" \"\\u{20f0}\") (re.range \"\\u{2102}\" \"\\u{2102}\") (re.range \"\\u{2107}\" \"\\u{2107}\") (re.range \"\\u{210a}\" \"\\u{2113}\") (re.range \"\\u{2115}\" \"\\u{2115}\") (re.range \"\\u{2119}\" \"\\u{211d}\") (re.range \"\\u{2124}\" \"\\u{2124}\") (re.range \"\\u{2126}\" \"\\u{2126}\") (re.range \"\\u{2128}\" \"\\u{2128}\") (re.range \"\\u{212a}\" \"\\u{212d}\") (re.range \"\\u{212f}\" \"\\u{2139}\") (re.range \"\\u{213c}\" \"\\u{213f}\") (re.range \"\\u{2145}\" \"\\u{2149}\") (re.range \"\\u{214e}\" \"\\u{214e}\") (re.range \"\\u{2160}\" \"\\u{2188}\") (re.range \"\\u{24b6}\" \"\\u{24e9}\") (re.range \"\\u{2c00}\" \"\\u{2c2e}\") (re.range \"\\u{2c30}\" \"\\u{2c5e}\") (re.range \"\\u{2c60}\" \"\\u{2ce4}\") (re.range \"\\u{2ceb}\" \"\\u{2cf3}\") (re.range \"\\u{2d00}\" \"\\u{2d25}\") (re.range \"\\u{2d27}\" \"\\u{2d27}\") (re.range \"\\u{2d2d}\" \"\\u{2d2d}\") (re.range \"\\u{2d30}\" \"\\u{2d67}\") (re.range \"\\u{2d6f}\" \"\\u{2d6f}\") (re.range \"\\u{2d7f}\" \"\\u{2d96}\") (re.range \"\\u{2da0}\" \"\\u{2da6}\") (re.range \"\\u{2da8}\" \"\\u{2dae}\") (re.range \"\\u{2db0}\" \"\\u{2db6}\") (re.range \"\\u{2db8}\" \"\\u{2dbe}\") (re.range \"\\u{2dc0}\" \"\\u{2dc6}\") (re.range \"\\u{2dc8}\" \"\\u{2dce}\") (re.range \"\\u{2dd0}\" \"\\u{2dd6}\") (re.range \"\\u{2dd8}\" \"\\u{2dde}\") (re.range \"\\u{2de0}\" \"\\u{2dff}\") (re.range \"\\u{2e2f}\" \"\\u{2e2f}\") (re.range \"\\u{3005}\" \"\\u{3007}\") (re.range \"\\u{3021}\" \"\\u{302f}\") (re.range \"\\u{3031}\" \"\\u{3035}\") (re.range \"\\u{3038}\" \"\\u{303c}\") (re.range \"\\u{3041}\" \"\\u{3096}\") (re.range \"\\u{3099}\" \"\\u{309a}\") (re.range \"\\u{309d}\" \"\\u{309f}\") (re.range \"\\u{30a1}\" \"\\u{30fa}\") (re.range \"\\u{30fc}\" \"\\u{30ff}\") (re.range \"\\u{3105}\" \"\\u{312e}\") (re.range \"\\u{3131}\" \"\\u{318e}\") (re.range \"\\u{31a0}\" \"\\u{31ba}\") (re.range \"\\u{31f0}\" \"\\u{31ff}\") (re.range \"\\u{3400}\" \"\\u{4db5}\") (re.range \"\\u{4e00}\" \"\\u{9fef}\") (re.range \"\\u{a000}\" \"\\u{a48c}\") (re.range \"\\u{a4d0}\" \"\\u{a4fd}\") (re.range \"\\u{a500}\" \"\\u{a60c}\") (re.range \"\\u{a610}\" \"\\u{a62b}\") (re.range \"\\u{a640}\" \"\\u{a672}\") (re.range \"\\u{a674}\" \"\\u{a67d}\") (re.range \"\\u{a67f}\" \"\\u{a6f1}\") (re.range \"\\u{a717}\" \"\\u{a71f}\") (re.range \"\\u{a722}\" \"\\u{a788}\") (re.range \"\\u{a78b}\" \"\\u{a7ae}\") (re.range \"\\u{a7b0}\" \"\\u{a7b7}\") (re.range \"\\u{a7f7}\" \"\\u{a827}\") (re.range \"\\u{a840}\" \"\\u{a873}\") (re.range \"\\u{a880}\" \"\\u{a8c5}\") (re.range \"\\u{a8d0}\" \"\\u{a8d9}\") (re.range \"\\u{a8e0}\" \"\\u{a8f7}\") (re.range \"\\u{a8fb}\" \"\\u{a8fb}\") (re.range \"\\u{a8fd}\" \"\\u{a8fd}\") (re.range \"\\u{a900}\" \"\\u{a92d}\") (re.range \"\\u{a930}\" \"\\u{a953}\") (re.range \"\\u{a960}\" \"\\u{a97c}\") (re.range \"\\u{a980}\" \"\\u{a9c0}\") (re.range \"\\u{a9cf}\" \"\\u{a9d9}\") (re.range \"\\u{a9e0}\" \"\\u{a9fe}\") (re.range \"\\u{aa00}\" \"\\u{aa36}\") (re.range \"\\u{aa40}\" \"\\u{aa4d}\") (re.range \"\\u{aa50}\" \"\\u{aa59}\") (re.range \"\\u{aa60}\" \"\\u{aa76}\") (re.range \"\\u{aa7a}\" \"\\u{aac2}\") (re.range \"\\u{aadb}\" \"\\u{aadd}\") (re.range \"\\u{aae0}\" \"\\u{aaef}\") (re.range \"\\u{aaf2}\" \"\\u{aaf6}\") (re.range \"\\u{ab01}\" \"\\u{ab06}\") (re.range \"\\u{ab09}\" \"\\u{ab0e}\") (re.range \"\\u{ab11}\" \"\\u{ab16}\") (re.range \"\\u{ab20}\" \"\\u{ab26}\") (re.range \"\\u{ab28}\" \"\\u{ab2e}\") (re.range \"\\u{ab30}\" \"\\u{ab5a}\") (re.range \"\\u{ab5c}\" \"\\u{ab65}\") (re.range \"\\u{ab70}\" \"\\u{abea}\") (re.range \"\\u{abec}\" \"\\u{abed}\") (re.range \"\\u{abf0}\" \"\\u{abf9}\") (re.range \"\\u{ac00}\" \"\\u{d7a3}\") (re.range \"\\u{d7b0}\" \"\\u{d7c6}\") (re.range \"\\u{d7cb}\" \"\\u{d7fb}\") (re.range \"\\u{f900}\" \"\\u{fa6d}\") (re.range \"\\u{fa70}\" \"\\u{fad9}\") (re.range \"\\u{fb00}\" \"\\u{fb06}\") (re.range \"\\u{fb13}\" \"\\u{fb17}\") (re.range \"\\u{fb1d}\" \"\\u{fb28}\") (re.range \"\\u{fb2a}\" \"\\u{fb36}\") (re.range \"\\u{fb38}\" \"\\u{fb3c}\") (re.range \"\\u{fb3e}\" \"\\u{fb3e}\") (re.range \"\\u{fb40}\" \"\\u{fb41}\") (re.range \"\\u{fb43}\" \"\\u{fb44}\") (re.range \"\\u{fb46}\" \"\\u{fbb1}\") (re.range \"\\u{fbd3}\" \"\\u{fd3d}\") (re.range \"\\u{fd50}\" \"\\u{fd8f}\") (re.range \"\\u{fd92}\" \"\\u{fdc7}\") (re.range \"\\u{fdf0}\" \"\\u{fdfb}\") (re.range \"\\u{fe00}\" \"\\u{fe0f}\") (re.range \"\\u{fe20}\" \"\\u{fe2f}\") (re.range \"\\u{fe33}\" \"\\u{fe34}\") (re.range \"\\u{fe4d}\" \"\\u{fe4f}\") (re.range \"\\u{fe70}\" \"\\u{fe74}\") (re.range \"\\u{fe76}\" \"\\u{fefc}\") (re.range \"\\u{ff10}\" \"\\u{ff19}\") (re.range \"\\u{ff21}\" \"\\u{ff3a}\") (re.range \"\\u{ff3f}\" \"\\u{ff3f}\") (re.range \"\\u{ff41}\" \"\\u{ff5a}\") (re.range \"\\u{ff66}\" \"\\u{ffbe}\") (re.range \"\\u{ffc2}\" \"\\u{ffc7}\") (re.range \"\\u{ffca}\" \"\\u{ffcf}\") (re.range \"\\u{ffd2}\" \"\\u{ffd7}\") (re.range \"\\u{ffda}\" \"\\u{ffdc}\") (re.range \"\\u{10000}\" \"\\u{1000b}\") (re.range \"\\u{1000d}\" \"\\u{10026}\") (re.range \"\\u{10028}\" \"\\u{1003a}\") (re.range \"\\u{1003c}\" \"\\u{1003d}\") (re.range \"\\u{1003f}\" \"\\u{1004d}\") (re.range \"\\u{10050}\" \"\\u{1005d}\") (re.range \"\\u{10080}\" \"\\u{100fa}\") (re.range \"\\u{10140}\" \"\\u{10174}\") (re.range \"\\u{101fd}\" \"\\u{101fd}\") (re.range \"\\u{10280}\" \"\\u{1029c}\") (re.range \"\\u{102a0}\" \"\\u{102d0}\") (re.range \"\\u{102e0}\" \"\\u{102e0}\") (re.range \"\\u{10300}\" \"\\u{1031f}\") (re.range \"\\u{1032d}\" \"\\u{1034a}\") (re.range \"\\u{10350}\" \"\\u{1037a}\") (re.range \"\\u{10380}\" \"\\u{1039d}\") (re.range \"\\u{103a0}\" \"\\u{103c3}\") (re.range \"\\u{103c8}\" \"\\u{103cf}\") (re.range \"\\u{103d1}\" \"\\u{103d5}\") (re.range \"\\u{10400}\" \"\\u{1049d}\") (re.range \"\\u{104a0}\" \"\\u{104a9}\") (re.range \"\\u{104b0}\" \"\\u{104d3}\") (re.range \"\\u{104d8}\" \"\\u{104fb}\") (re.range \"\\u{10500}\" \"\\u{10527}\") (re.range \"\\u{10530}\" \"\\u{10563}\") (re.range \"\\u{10600}\" \"\\u{10736}\") (re.range \"\\u{10740}\" \"\\u{10755}\") (re.range \"\\u{10760}\" \"\\u{10767}\") (re.range \"\\u{10800}\" \"\\u{10805}\") (re.range \"\\u{10808}\" \"\\u{10808}\") (re.range \"\\u{1080a}\" \"\\u{10835}\") (re.range \"\\u{10837}\" \"\\u{10838}\") (re.range \"\\u{1083c}\" \"\\u{1083c}\") (re.range \"\\u{1083f}\" \"\\u{10855}\") (re.range \"\\u{10860}\" \"\\u{10876}\") (re.range \"\\u{10880}\" \"\\u{1089e}\") (re.range \"\\u{108e0}\" \"\\u{108f2}\") (re.range \"\\u{108f4}\" \"\\u{108f5}\") (re.range \"\\u{10900}\" \"\\u{10915}\") (re.range \"\\u{10920}\" \"\\u{10939}\") (re.range \"\\u{10980}\" \"\\u{109b7}\") (re.range \"\\u{109be}\" \"\\u{109bf}\") (re.range \"\\u{10a00}\" \"\\u{10a03}\") (re.range \"\\u{10a05}\" \"\\u{10a06}\") (re.range \"\\u{10a0c}\" \"\\u{10a13}\") (re.range \"\\u{10a15}\" \"\\u{10a17}\") (re.range \"\\u{10a19}\" \"\\u{10a33}\") (re.range \"\\u{10a38}\" \"\\u{10a3a}\") (re.range \"\\u{10a3f}\" \"\\u{10a3f}\") (re.range \"\\u{10a60}\" \"\\u{10a7c}\") (re.range \"\\u{10a80}\" \"\\u{10a9c}\") (re.range \"\\u{10ac0}\" \"\\u{10ac7}\") (re.range \"\\u{10ac9}\" \"\\u{10ae6}\") (re.range \"\\u{10b00}\" \"\\u{10b35}\") (re.range \"\\u{10b40}\" \"\\u{10b55}\") (re.range \"\\u{10b60}\" \"\\u{10b72}\") (re.range \"\\u{10b80}\" \"\\u{10b91}\") (re.range \"\\u{10c00}\" \"\\u{10c48}\") (re.range \"\\u{10c80}\" \"\\u{10cb2}\") (re.range \"\\u{10cc0}\" \"\\u{10cf2}\") (re.range \"\\u{11000}\" \"\\u{11046}\") (re.range \"\\u{11066}\" \"\\u{1106f}\") (re.range \"\\u{1107f}\" \"\\u{110ba}\") (re.range \"\\u{110d0}\" \"\\u{110e8}\") (re.range \"\\u{110f0}\" \"\\u{110f9}\") (re.range \"\\u{11100}\" \"\\u{11134}\") (re.range \"\\u{11136}\" \"\\u{1113f}\") (re.range \"\\u{11150}\" \"\\u{11173}\") (re.range \"\\u{11176}\" \"\\u{11176}\") (re.range \"\\u{11180}\" \"\\u{111c4}\") (re.range \"\\u{111ca}\" \"\\u{111cc}\") (re.range \"\\u{111d0}\" \"\\u{111da}\") (re.range \"\\u{111dc}\" \"\\u{111dc}\") (re.range \"\\u{11200}\" \"\\u{11211}\") (re.range \"\\u{11213}\" \"\\u{11237}\") (re.range \"\\u{1123e}\" \"\\u{1123e}\") (re.range \"\\u{11280}\" \"\\u{11286}\") (re.range \"\\u{11288}\" \"\\u{11288}\") (re.range \"\\u{1128a}\" \"\\u{1128d}\") (re.range \"\\u{1128f}\" \"\\u{1129d}\") (re.range \"\\u{1129f}\" \"\\u{112a8}\") (re.range \"\\u{112b0}\" \"\\u{112ea}\") (re.range \"\\u{112f0}\" \"\\u{112f9}\") (re.range \"\\u{11300}\" \"\\u{11303}\") (re.range \"\\u{11305}\" \"\\u{1130c}\") (re.range \"\\u{1130f}\" \"\\u{11310}\") (re.range \"\\u{11313}\" \"\\u{11328}\") (re.range \"\\u{1132a}\" \"\\u{11330}\") (re.range \"\\u{11332}\" \"\\u{11333}\") (re.range \"\\u{11335}\" \"\\u{11339}\") (re.range \"\\u{1133c}\" \"\\u{11344}\") (re.range \"\\u{11347}\" \"\\u{11348}\") (re.range \"\\u{1134b}\" \"\\u{1134d}\") (re.range \"\\u{11350}\" \"\\u{11350}\") (re.range \"\\u{11357}\" \"\\u{11357}\") (re.range \"\\u{1135d}\" \"\\u{11363}\") (re.range \"\\u{11366}\" \"\\u{1136c}\") (re.range \"\\u{11370}\" \"\\u{11374}\") (re.range \"\\u{11400}\" \"\\u{1144a}\") (re.range \"\\u{11450}\" \"\\u{11459}\") (re.range \"\\u{11480}\" \"\\u{114c5}\") (re.range \"\\u{114c7}\" \"\\u{114c7}\") (re.range \"\\u{114d0}\" \"\\u{114d9}\") (re.range \"\\u{11580}\" \"\\u{115b5}\") (re.range \"\\u{115b8}\" \"\\u{115c0}\") (re.range \"\\u{115d8}\" \"\\u{115dd}\") (re.range \"\\u{11600}\" \"\\u{11640}\") (re.range \"\\u{11644}\" \"\\u{11644}\") (re.range \"\\u{11650}\" \"\\u{11659}\") (re.range \"\\u{11680}\" \"\\u{116b7}\") (re.range \"\\u{116c0}\" \"\\u{116c9}\") (re.range \"\\u{11700}\" \"\\u{11719}\") (re.range \"\\u{1171d}\" \"\\u{1172b}\") (re.range \"\\u{11730}\" \"\\u{11739}\") (re.range \"\\u{118a0}\" \"\\u{118e9}\") (re.range \"\\u{118ff}\" \"\\u{118ff}\") (re.range \"\\u{11a00}\" \"\\u{11a3e}\") (re.range \"\\u{11a47}\" \"\\u{11a47}\") (re.range \"\\u{11a50}\" \"\\u{11a83}\") (re.range \"\\u{11a86}\" \"\\u{11a99}\") (re.range \"\\u{11ac0}\" \"\\u{11af8}\") (re.range \"\\u{11c00}\" \"\\u{11c08}\") (re.range \"\\u{11c0a}\" \"\\u{11c36}\") (re.range \"\\u{11c38}\" \"\\u{11c40}\") (re.range \"\\u{11c50}\" \"\\u{11c59}\") (re.range \"\\u{11c72}\" \"\\u{11c8f}\") (re.range \"\\u{11c92}\" \"\\u{11ca7}\") (re.range \"\\u{11ca9}\" \"\\u{11cb6}\") (re.range \"\\u{11d00}\" \"\\u{11d06}\") (re.range \"\\u{11d08}\" \"\\u{11d09}\") (re.range \"\\u{11d0b}\" \"\\u{11d36}\") (re.range \"\\u{11d3a}\" \"\\u{11d3a}\") (re.range \"\\u{11d3c}\" \"\\u{11d3d}\") (re.range \"\\u{11d3f}\" \"\\u{11d47}\") (re.range \"\\u{11d50}\" \"\\u{11d59}\") (re.range \"\\u{12000}\" \"\\u{12399}\") (re.range \"\\u{12400}\" \"\\u{1246e}\") (re.range \"\\u{12480}\" \"\\u{12543}\") (re.range \"\\u{13000}\" \"\\u{1342e}\") (re.range \"\\u{14400}\" \"\\u{14646}\") (re.range \"\\u{16800}\" \"\\u{16a38}\") (re.range \"\\u{16a40}\" \"\\u{16a5e}\") (re.range \"\\u{16a60}\" \"\\u{16a69}\") (re.range \"\\u{16ad0}\" \"\\u{16aed}\") (re.range \"\\u{16af0}\" \"\\u{16af4}\") (re.range \"\\u{16b00}\" \"\\u{16b36}\") (re.range \"\\u{16b40}\" \"\\u{16b43}\") (re.range \"\\u{16b50}\" \"\\u{16b59}\") (re.range \"\\u{16b63}\" \"\\u{16b77}\") (re.range \"\\u{16b7d}\" \"\\u{16b8f}\") (re.range \"\\u{16f00}\" \"\\u{16f44}\") (re.range \"\\u{16f50}\" \"\\u{16f7e}\") (re.range \"\\u{16f8f}\" \"\\u{16f9f}\") (re.range \"\\u{16fe0}\" \"\\u{16fe1}\") (re.range \"\\u{17000}\" \"\\u{187ec}\") (re.range \"\\u{18800}\" \"\\u{18af2}\") (re.range \"\\u{1b000}\" \"\\u{1b11e}\") (re.range \"\\u{1b170}\" \"\\u{1b2fb}\") (re.range \"\\u{1bc00}\" \"\\u{1bc6a}\") (re.range \"\\u{1bc70}\" \"\\u{1bc7c}\") (re.range \"\\u{1bc80}\" \"\\u{1bc88}\") (re.range \"\\u{1bc90}\" \"\\u{1bc99}\") (re.range \"\\u{1bc9d}\" \"\\u{1bc9e}\") (re.range \"\\u{1d165}\" \"\\u{1d169}\") (re.range \"\\u{1d16d}\" \"\\u{1d172}\") (re.range \"\\u{1d17b}\" \"\\u{1d182}\") (re.range \"\\u{1d185}\" \"\\u{1d18b}\") (re.range \"\\u{1d1aa}\" \"\\u{1d1ad}\") (re.range \"\\u{1d242}\" \"\\u{1d244}\") (re.range \"\\u{1d400}\" \"\\u{1d454}\") (re.range \"\\u{1d456}\" \"\\u{1d49c}\") (re.range \"\\u{1d49e}\" \"\\u{1d49f}\") (re.range \"\\u{1d4a2}\" \"\\u{1d4a2}\") (re.range \"\\u{1d4a5}\" \"\\u{1d4a6}\") (re.range \"\\u{1d4a9}\" \"\\u{1d4ac}\") (re.range \"\\u{1d4ae}\" \"\\u{1d4b9}\") (re.range \"\\u{1d4bb}\" \"\\u{1d4bb}\") (re.range \"\\u{1d4bd}\" \"\\u{1d4c3}\") (re.range \"\\u{1d4c5}\" \"\\u{1d505}\") (re.range \"\\u{1d507}\" \"\\u{1d50a}\") (re.range \"\\u{1d50d}\" \"\\u{1d514}\") (re.range \"\\u{1d516}\" \"\\u{1d51c}\") (re.range \"\\u{1d51e}\" \"\\u{1d539}\") (re.range \"\\u{1d53b}\" \"\\u{1d53e}\") (re.range \"\\u{1d540}\" \"\\u{1d544}\") (re.range \"\\u{1d546}\" \"\\u{1d546}\") (re.range \"\\u{1d54a}\" \"\\u{1d550}\") (re.range \"\\u{1d552}\" \"\\u{1d6a5}\") (re.range \"\\u{1d6a8}\" \"\\u{1d6c0}\") (re.range \"\\u{1d6c2}\" \"\\u{1d6da}\") (re.range \"\\u{1d6dc}\" \"\\u{1d6fa}\") (re.range \"\\u{1d6fc}\" \"\\u{1d714}\") (re.range \"\\u{1d716}\" \"\\u{1d734}\") (re.range \"\\u{1d736}\" \"\\u{1d74e}\") (re.range \"\\u{1d750}\" \"\\u{1d76e}\") (re.range \"\\u{1d770}\" \"\\u{1d788}\") (re.range \"\\u{1d78a}\" \"\\u{1d7a8}\") (re.range \"\\u{1d7aa}\" \"\\u{1d7c2}\") (re.range \"\\u{1d7c4}\" \"\\u{1d7cb}\") (re.range \"\\u{1d7ce}\" \"\\u{1d7ff}\") (re.range \"\\u{1da00}\" \"\\u{1da36}\") (re.range \"\\u{1da3b}\" \"\\u{1da6c}\") (re.range \"\\u{1da75}\" \"\\u{1da75}\") (re.range \"\\u{1da84}\" \"\\u{1da84}\") (re.range \"\\u{1da9b}\" \"\\u{1da9f}\") (re.range \"\\u{1daa1}\" \"\\u{1daaf}\") (re.range \"\\u{1e000}\" \"\\u{1e006}\") (re.range \"\\u{1e008}\" \"\\u{1e018}\") (re.range \"\\u{1e01b}\" \"\\u{1e021}\") (re.range \"\\u{1e023}\" \"\\u{1e024}\") (re.range \"\\u{1e026}\" \"\\u{1e02a}\") (re.range \"\\u{1e800}\" \"\\u{1e8c4}\") (re.range \"\\u{1e8d0}\" \"\\u{1e8d6}\") (re.range \"\\u{1e900}\" \"\\u{1e94a}\") (re.range \"\\u{1e950}\" \"\\u{1e959}\") (re.range \"\\u{1ee00}\" \"\\u{1ee03}\") (re.range \"\\u{1ee05}\" \"\\u{1ee1f}\") (re.range \"\\u{1ee21}\" \"\\u{1ee22}\") (re.range \"\\u{1ee24}\" \"\\u{1ee24}\") (re.range \"\\u{1ee27}\" \"\\u{1ee27}\") (re.range \"\\u{1ee29}\" \"\\u{1ee32}\") (re.range \"\\u{1ee34}\" \"\\u{1ee37}\") (re.range \"\\u{1ee39}\" \"\\u{1ee39}\") (re.range \"\\u{1ee3b}\" \"\\u{1ee3b}\") (re.range \"\\u{1ee42}\" \"\\u{1ee42}\") (re.range \"\\u{1ee47}\" \"\\u{1ee47}\") (re.range \"\\u{1ee49}\" \"\\u{1ee49}\") (re.range \"\\u{1ee4b}\" \"\\u{1ee4b}\") (re.range \"\\u{1ee4d}\" \"\\u{1ee4f}\") (re.range \"\\u{1ee51}\" \"\\u{1ee52}\") (re.range \"\\u{1ee54}\" \"\\u{1ee54}\") (re.range \"\\u{1ee57}\" \"\\u{1ee57}\") (re.range \"\\u{1ee59}\" \"\\u{1ee59}\") (re.range \"\\u{1ee5b}\" \"\\u{1ee5b}\") (re.range \"\\u{1ee5d}\" \"\\u{1ee5d}\") (re.range \"\\u{1ee5f}\" \"\\u{1ee5f}\") (re.range \"\\u{1ee61}\" \"\\u{1ee62}\") (re.range \"\\u{1ee64}\" \"\\u{1ee64}\") (re.range \"\\u{1ee67}\" \"\\u{1ee6a}\") (re.range \"\\u{1ee6c}\" \"\\u{1ee72}\") (re.range \"\\u{1ee74}\" \"\\u{1ee77}\") (re.range \"\\u{1ee79}\" \"\\u{1ee7c}\") (re.range \"\\u{1ee7e}\" \"\\u{1ee7e}\") (re.range \"\\u{1ee80}\" \"\\u{1ee89}\") (re.range \"\\u{1ee8b}\" \"\\u{1ee9b}\") (re.range \"\\u{1eea1}\" \"\\u{1eea3}\") (re.range \"\\u{1eea5}\" \"\\u{1eea9}\") (re.range \"\\u{1eeab}\" \"\\u{1eebb}\") (re.range \"\\u{1f130}\" \"\\u{1f149}\") (re.range \"\\u{1f150}\" \"\\u{1f169}\") (re.range \"\\u{1f170}\" \"\\u{1f189}\") (re.range \"\\u{20000}\" \"\\u{2a6d6}\") (re.range \"\\u{2a700}\" \"\\u{2b734}\") (re.range \"\\u{2b740}\" \"\\u{2b81d}\") (re.range \"\\u{2b820}\" \"\\u{2cea1}\") (re.range \"\\u{2ceb0}\" \"\\u{2ebe0}\") (re.range \"\\u{2f800}\" \"\\u{2fa1d}\") (re.range \"\\u{e0100}\" \"\\u{e01ef}\"))";
    private static String notWordChars = "(re.union (re.range \"\\u{00}\" \"\\u{2f}\") (re.range \"\\u{3a}\" \"\\u{40}\") (re.range \"\\u{5b}\" \"\\u{5e}\") (re.range \"\\u{60}\" \"\\u{60}\") (re.range \"\\u{7b}\" \"\\u{a9}\") (re.range \"\\u{ab}\" \"\\u{b4}\") (re.range \"\\u{b6}\" \"\\u{b9}\") (re.range \"\\u{bb}\" \"\\u{bf}\") (re.range \"\\u{d7}\" \"\\u{d7}\") (re.range \"\\u{f7}\" \"\\u{f7}\") (re.range \"\\u{2c2}\" \"\\u{2c5}\") (re.range \"\\u{2d2}\" \"\\u{2df}\") (re.range \"\\u{2e5}\" \"\\u{2eb}\") (re.range \"\\u{2ed}\" \"\\u{2ed}\") (re.range \"\\u{2ef}\" \"\\u{2ff}\") (re.range \"\\u{375}\" \"\\u{375}\") (re.range \"\\u{378}\" \"\\u{379}\") (re.range \"\\u{37e}\" \"\\u{37e}\") (re.range \"\\u{380}\" \"\\u{385}\") (re.range \"\\u{387}\" \"\\u{387}\") (re.range \"\\u{38b}\" \"\\u{38b}\") (re.range \"\\u{38d}\" \"\\u{38d}\") (re.range \"\\u{3a2}\" \"\\u{3a2}\") (re.range \"\\u{3f6}\" \"\\u{3f6}\") (re.range \"\\u{482}\" \"\\u{482}\") (re.range \"\\u{530}\" \"\\u{530}\") (re.range \"\\u{557}\" \"\\u{558}\") (re.range \"\\u{55a}\" \"\\u{560}\") (re.range \"\\u{588}\" \"\\u{590}\") (re.range \"\\u{5be}\" \"\\u{5be}\") (re.range \"\\u{5c0}\" \"\\u{5c0}\") (re.range \"\\u{5c3}\" \"\\u{5c3}\") (re.range \"\\u{5c6}\" \"\\u{5c6}\") (re.range \"\\u{5c8}\" \"\\u{5cf}\") (re.range \"\\u{5eb}\" \"\\u{5ef}\") (re.range \"\\u{5f3}\" \"\\u{60f}\") (re.range \"\\u{61b}\" \"\\u{61f}\") (re.range \"\\u{66a}\" \"\\u{66d}\") (re.range \"\\u{6d4}\" \"\\u{6d4}\") (re.range \"\\u{6dd}\" \"\\u{6de}\") (re.range \"\\u{6e9}\" \"\\u{6e9}\") (re.range \"\\u{6fd}\" \"\\u{6fe}\") (re.range \"\\u{700}\" \"\\u{70f}\") (re.range \"\\u{74b}\" \"\\u{74c}\") (re.range \"\\u{7b2}\" \"\\u{7bf}\") (re.range \"\\u{7f6}\" \"\\u{7f9}\") (re.range \"\\u{7fb}\" \"\\u{7ff}\") (re.range \"\\u{82e}\" \"\\u{83f}\") (re.range \"\\u{85c}\" \"\\u{85f}\") (re.range \"\\u{86b}\" \"\\u{89f}\") (re.range \"\\u{8b5}\" \"\\u{8b5}\") (re.range \"\\u{8be}\" \"\\u{8d3}\") (re.range \"\\u{8e2}\" \"\\u{8e2}\") (re.range \"\\u{964}\" \"\\u{965}\") (re.range \"\\u{970}\" \"\\u{970}\") (re.range \"\\u{984}\" \"\\u{984}\") (re.range \"\\u{98d}\" \"\\u{98e}\") (re.range \"\\u{991}\" \"\\u{992}\") (re.range \"\\u{9a9}\" \"\\u{9a9}\") (re.range \"\\u{9b1}\" \"\\u{9b1}\") (re.range \"\\u{9b3}\" \"\\u{9b5}\") (re.range \"\\u{9ba}\" \"\\u{9bb}\") (re.range \"\\u{9c5}\" \"\\u{9c6}\") (re.range \"\\u{9c9}\" \"\\u{9ca}\") (re.range \"\\u{9cf}\" \"\\u{9d6}\") (re.range \"\\u{9d8}\" \"\\u{9db}\") (re.range \"\\u{9de}\" \"\\u{9de}\") (re.range \"\\u{9e4}\" \"\\u{9e5}\") (re.range \"\\u{9f2}\" \"\\u{9fb}\") (re.range \"\\u{9fd}\" \"\\u{a00}\") (re.range \"\\u{a04}\" \"\\u{a04}\") (re.range \"\\u{a0b}\" \"\\u{a0e}\") (re.range \"\\u{a11}\" \"\\u{a12}\") (re.range \"\\u{a29}\" \"\\u{a29}\") (re.range \"\\u{a31}\" \"\\u{a31}\") (re.range \"\\u{a34}\" \"\\u{a34}\") (re.range \"\\u{a37}\" \"\\u{a37}\") (re.range \"\\u{a3a}\" \"\\u{a3b}\") (re.range \"\\u{a3d}\" \"\\u{a3d}\") (re.range \"\\u{a43}\" \"\\u{a46}\") (re.range \"\\u{a49}\" \"\\u{a4a}\") (re.range \"\\u{a4e}\" \"\\u{a50}\") (re.range \"\\u{a52}\" \"\\u{a58}\") (re.range \"\\u{a5d}\" \"\\u{a5d}\") (re.range \"\\u{a5f}\" \"\\u{a65}\") (re.range \"\\u{a76}\" \"\\u{a80}\") (re.range \"\\u{a84}\" \"\\u{a84}\") (re.range \"\\u{a8e}\" \"\\u{a8e}\") (re.range \"\\u{a92}\" \"\\u{a92}\") (re.range \"\\u{aa9}\" \"\\u{aa9}\") (re.range \"\\u{ab1}\" \"\\u{ab1}\") (re.range \"\\u{ab4}\" \"\\u{ab4}\") (re.range \"\\u{aba}\" \"\\u{abb}\") (re.range \"\\u{ac6}\" \"\\u{ac6}\") (re.range \"\\u{aca}\" \"\\u{aca}\") (re.range \"\\u{ace}\" \"\\u{acf}\") (re.range \"\\u{ad1}\" \"\\u{adf}\") (re.range \"\\u{ae4}\" \"\\u{ae5}\") (re.range \"\\u{af0}\" \"\\u{af8}\") (re.range \"\\u{b00}\" \"\\u{b00}\") (re.range \"\\u{b04}\" \"\\u{b04}\") (re.range \"\\u{b0d}\" \"\\u{b0e}\") (re.range \"\\u{b11}\" \"\\u{b12}\") (re.range \"\\u{b29}\" \"\\u{b29}\") (re.range \"\\u{b31}\" \"\\u{b31}\") (re.range \"\\u{b34}\" \"\\u{b34}\") (re.range \"\\u{b3a}\" \"\\u{b3b}\") (re.range \"\\u{b45}\" \"\\u{b46}\") (re.range \"\\u{b49}\" \"\\u{b4a}\") (re.range \"\\u{b4e}\" \"\\u{b55}\") (re.range \"\\u{b58}\" \"\\u{b5b}\") (re.range \"\\u{b5e}\" \"\\u{b5e}\") (re.range \"\\u{b64}\" \"\\u{b65}\") (re.range \"\\u{b70}\" \"\\u{b70}\") (re.range \"\\u{b72}\" \"\\u{b81}\") (re.range \"\\u{b84}\" \"\\u{b84}\") (re.range \"\\u{b8b}\" \"\\u{b8d}\") (re.range \"\\u{b91}\" \"\\u{b91}\") (re.range \"\\u{b96}\" \"\\u{b98}\") (re.range \"\\u{b9b}\" \"\\u{b9b}\") (re.range \"\\u{b9d}\" \"\\u{b9d}\") (re.range \"\\u{ba0}\" \"\\u{ba2}\") (re.range \"\\u{ba5}\" \"\\u{ba7}\") (re.range \"\\u{bab}\" \"\\u{bad}\") (re.range \"\\u{bba}\" \"\\u{bbd}\") (re.range \"\\u{bc3}\" \"\\u{bc5}\") (re.range \"\\u{bc9}\" \"\\u{bc9}\") (re.range \"\\u{bce}\" \"\\u{bcf}\") (re.range \"\\u{bd1}\" \"\\u{bd6}\") (re.range \"\\u{bd8}\" \"\\u{be5}\") (re.range \"\\u{bf0}\" \"\\u{bff}\") (re.range \"\\u{c04}\" \"\\u{c04}\") (re.range \"\\u{c0d}\" \"\\u{c0d}\") (re.range \"\\u{c11}\" \"\\u{c11}\") (re.range \"\\u{c29}\" \"\\u{c29}\") (re.range \"\\u{c3a}\" \"\\u{c3c}\") (re.range \"\\u{c45}\" \"\\u{c45}\") (re.range \"\\u{c49}\" \"\\u{c49}\") (re.range \"\\u{c4e}\" \"\\u{c54}\") (re.range \"\\u{c57}\" \"\\u{c57}\") (re.range \"\\u{c5b}\" \"\\u{c5f}\") (re.range \"\\u{c64}\" \"\\u{c65}\") (re.range \"\\u{c70}\" \"\\u{c7f}\") (re.range \"\\u{c84}\" \"\\u{c84}\") (re.range \"\\u{c8d}\" \"\\u{c8d}\") (re.range \"\\u{c91}\" \"\\u{c91}\") (re.range \"\\u{ca9}\" \"\\u{ca9}\") (re.range \"\\u{cb4}\" \"\\u{cb4}\") (re.range \"\\u{cba}\" \"\\u{cbb}\") (re.range \"\\u{cc5}\" \"\\u{cc5}\") (re.range \"\\u{cc9}\" \"\\u{cc9}\") (re.range \"\\u{cce}\" \"\\u{cd4}\") (re.range \"\\u{cd7}\" \"\\u{cdd}\") (re.range \"\\u{cdf}\" \"\\u{cdf}\") (re.range \"\\u{ce4}\" \"\\u{ce5}\") (re.range \"\\u{cf0}\" \"\\u{cf0}\") (re.range \"\\u{cf3}\" \"\\u{cff}\") (re.range \"\\u{d04}\" \"\\u{d04}\") (re.range \"\\u{d0d}\" \"\\u{d0d}\") (re.range \"\\u{d11}\" \"\\u{d11}\") (re.range \"\\u{d45}\" \"\\u{d45}\") (re.range \"\\u{d49}\" \"\\u{d49}\") (re.range \"\\u{d4f}\" \"\\u{d53}\") (re.range \"\\u{d58}\" \"\\u{d5e}\") (re.range \"\\u{d64}\" \"\\u{d65}\") (re.range \"\\u{d70}\" \"\\u{d79}\") (re.range \"\\u{d80}\" \"\\u{d81}\") (re.range \"\\u{d84}\" \"\\u{d84}\") (re.range \"\\u{d97}\" \"\\u{d99}\") (re.range \"\\u{db2}\" \"\\u{db2}\") (re.range \"\\u{dbc}\" \"\\u{dbc}\") (re.range \"\\u{dbe}\" \"\\u{dbf}\") (re.range \"\\u{dc7}\" \"\\u{dc9}\") (re.range \"\\u{dcb}\" \"\\u{dce}\") (re.range \"\\u{dd5}\" \"\\u{dd5}\") (re.range \"\\u{dd7}\" \"\\u{dd7}\") (re.range \"\\u{de0}\" \"\\u{de5}\") (re.range \"\\u{df0}\" \"\\u{df1}\") (re.range \"\\u{df4}\" \"\\u{e00}\") (re.range \"\\u{e3b}\" \"\\u{e3f}\") (re.range \"\\u{e4f}\" \"\\u{e4f}\") (re.range \"\\u{e5a}\" \"\\u{e80}\") (re.range \"\\u{e83}\" \"\\u{e83}\") (re.range \"\\u{e85}\" \"\\u{e86}\") (re.range \"\\u{e89}\" \"\\u{e89}\") (re.range \"\\u{e8b}\" \"\\u{e8c}\") (re.range \"\\u{e8e}\" \"\\u{e93}\") (re.range \"\\u{e98}\" \"\\u{e98}\") (re.range \"\\u{ea0}\" \"\\u{ea0}\") (re.range \"\\u{ea4}\" \"\\u{ea4}\") (re.range \"\\u{ea6}\" \"\\u{ea6}\") (re.range \"\\u{ea8}\" \"\\u{ea9}\") (re.range \"\\u{eac}\" \"\\u{eac}\") (re.range \"\\u{eba}\" \"\\u{eba}\") (re.range \"\\u{ebe}\" \"\\u{ebf}\") (re.range \"\\u{ec5}\" \"\\u{ec5}\") (re.range \"\\u{ec7}\" \"\\u{ec7}\") (re.range \"\\u{ece}\" \"\\u{ecf}\") (re.range \"\\u{eda}\" \"\\u{edb}\") (re.range \"\\u{ee0}\" \"\\u{eff}\") (re.range \"\\u{f01}\" \"\\u{f17}\") (re.range \"\\u{f1a}\" \"\\u{f1f}\") (re.range \"\\u{f2a}\" \"\\u{f34}\") (re.range \"\\u{f36}\" \"\\u{f36}\") (re.range \"\\u{f38}\" \"\\u{f38}\") (re.range \"\\u{f3a}\" \"\\u{f3d}\") (re.range \"\\u{f48}\" \"\\u{f48}\") (re.range \"\\u{f6d}\" \"\\u{f70}\") (re.range \"\\u{f85}\" \"\\u{f85}\") (re.range \"\\u{f98}\" \"\\u{f98}\") (re.range \"\\u{fbd}\" \"\\u{fc5}\") (re.range \"\\u{fc7}\" \"\\u{fff}\") (re.range \"\\u{104a}\" \"\\u{104f}\") (re.range \"\\u{109e}\" \"\\u{109f}\") (re.range \"\\u{10c6}\" \"\\u{10c6}\") (re.range \"\\u{10c8}\" \"\\u{10cc}\") (re.range \"\\u{10ce}\" \"\\u{10cf}\") (re.range \"\\u{10fb}\" \"\\u{10fb}\") (re.range \"\\u{1249}\" \"\\u{1249}\") (re.range \"\\u{124e}\" \"\\u{124f}\") (re.range \"\\u{1257}\" \"\\u{1257}\") (re.range \"\\u{1259}\" \"\\u{1259}\") (re.range \"\\u{125e}\" \"\\u{125f}\") (re.range \"\\u{1289}\" \"\\u{1289}\") (re.range \"\\u{128e}\" \"\\u{128f}\") (re.range \"\\u{12b1}\" \"\\u{12b1}\") (re.range \"\\u{12b6}\" \"\\u{12b7}\") (re.range \"\\u{12bf}\" \"\\u{12bf}\") (re.range \"\\u{12c1}\" \"\\u{12c1}\") (re.range \"\\u{12c6}\" \"\\u{12c7}\") (re.range \"\\u{12d7}\" \"\\u{12d7}\") (re.range \"\\u{1311}\" \"\\u{1311}\") (re.range \"\\u{1316}\" \"\\u{1317}\") (re.range \"\\u{135b}\" \"\\u{135c}\") (re.range \"\\u{1360}\" \"\\u{137f}\") (re.range \"\\u{1390}\" \"\\u{139f}\") (re.range \"\\u{13f6}\" \"\\u{13f7}\") (re.range \"\\u{13fe}\" \"\\u{1400}\") (re.range \"\\u{166d}\" \"\\u{166e}\") (re.range \"\\u{1680}\" \"\\u{1680}\") (re.range \"\\u{169b}\" \"\\u{169f}\") (re.range \"\\u{16eb}\" \"\\u{16ed}\") (re.range \"\\u{16f9}\" \"\\u{16ff}\") (re.range \"\\u{170d}\" \"\\u{170d}\") (re.range \"\\u{1715}\" \"\\u{171f}\") (re.range \"\\u{1735}\" \"\\u{173f}\") (re.range \"\\u{1754}\" \"\\u{175f}\") (re.range \"\\u{176d}\" \"\\u{176d}\") (re.range \"\\u{1771}\" \"\\u{1771}\") (re.range \"\\u{1774}\" \"\\u{177f}\") (re.range \"\\u{17d4}\" \"\\u{17d6}\") (re.range \"\\u{17d8}\" \"\\u{17db}\") (re.range \"\\u{17de}\" \"\\u{17df}\") (re.range \"\\u{17ea}\" \"\\u{180a}\") (re.range \"\\u{180e}\" \"\\u{180f}\") (re.range \"\\u{181a}\" \"\\u{181f}\") (re.range \"\\u{1878}\" \"\\u{187f}\") (re.range \"\\u{18ab}\" \"\\u{18af}\") (re.range \"\\u{18f6}\" \"\\u{18ff}\") (re.range \"\\u{191f}\" \"\\u{191f}\") (re.range \"\\u{192c}\" \"\\u{192f}\") (re.range \"\\u{193c}\" \"\\u{1945}\") (re.range \"\\u{196e}\" \"\\u{196f}\") (re.range \"\\u{1975}\" \"\\u{197f}\") (re.range \"\\u{19ac}\" \"\\u{19af}\") (re.range \"\\u{19ca}\" \"\\u{19cf}\") (re.range \"\\u{19da}\" \"\\u{19ff}\") (re.range \"\\u{1a1c}\" \"\\u{1a1f}\") (re.range \"\\u{1a5f}\" \"\\u{1a5f}\") (re.range \"\\u{1a7d}\" \"\\u{1a7e}\") (re.range \"\\u{1a8a}\" \"\\u{1a8f}\") (re.range \"\\u{1a9a}\" \"\\u{1aa6}\") (re.range \"\\u{1aa8}\" \"\\u{1aaf}\") (re.range \"\\u{1abf}\" \"\\u{1aff}\") (re.range \"\\u{1b4c}\" \"\\u{1b4f}\") (re.range \"\\u{1b5a}\" \"\\u{1b6a}\") (re.range \"\\u{1b74}\" \"\\u{1b7f}\") (re.range \"\\u{1bf4}\" \"\\u{1bff}\") (re.range \"\\u{1c38}\" \"\\u{1c3f}\") (re.range \"\\u{1c4a}\" \"\\u{1c4c}\") (re.range \"\\u{1c7e}\" \"\\u{1c7f}\") (re.range \"\\u{1c89}\" \"\\u{1ccf}\") (re.range \"\\u{1cd3}\" \"\\u{1cd3}\") (re.range \"\\u{1cfa}\" \"\\u{1cff}\") (re.range \"\\u{1dfa}\" \"\\u{1dfa}\") (re.range \"\\u{1f16}\" \"\\u{1f17}\") (re.range \"\\u{1f1e}\" \"\\u{1f1f}\") (re.range \"\\u{1f46}\" \"\\u{1f47}\") (re.range \"\\u{1f4e}\" \"\\u{1f4f}\") (re.range \"\\u{1f58}\" \"\\u{1f58}\") (re.range \"\\u{1f5a}\" \"\\u{1f5a}\") (re.range \"\\u{1f5c}\" \"\\u{1f5c}\") (re.range \"\\u{1f5e}\" \"\\u{1f5e}\") (re.range \"\\u{1f7e}\" \"\\u{1f7f}\") (re.range \"\\u{1fb5}\" \"\\u{1fb5}\") (re.range \"\\u{1fbd}\" \"\\u{1fbd}\") (re.range \"\\u{1fbf}\" \"\\u{1fc1}\") (re.range \"\\u{1fc5}\" \"\\u{1fc5}\") (re.range \"\\u{1fcd}\" \"\\u{1fcf}\") (re.range \"\\u{1fd4}\" \"\\u{1fd5}\") (re.range \"\\u{1fdc}\" \"\\u{1fdf}\") (re.range \"\\u{1fed}\" \"\\u{1ff1}\") (re.range \"\\u{1ff5}\" \"\\u{1ff5}\") (re.range \"\\u{1ffd}\" \"\\u{200b}\") (re.range \"\\u{200e}\" \"\\u{203e}\") (re.range \"\\u{2041}\" \"\\u{2053}\") (re.range \"\\u{2055}\" \"\\u{2070}\") (re.range \"\\u{2072}\" \"\\u{207e}\") (re.range \"\\u{2080}\" \"\\u{208f}\") (re.range \"\\u{209d}\" \"\\u{20cf}\") (re.range \"\\u{20f1}\" \"\\u{2101}\") (re.range \"\\u{2103}\" \"\\u{2106}\") (re.range \"\\u{2108}\" \"\\u{2109}\") (re.range \"\\u{2114}\" \"\\u{2114}\") (re.range \"\\u{2116}\" \"\\u{2118}\") (re.range \"\\u{211e}\" \"\\u{2123}\") (re.range \"\\u{2125}\" \"\\u{2125}\") (re.range \"\\u{2127}\" \"\\u{2127}\") (re.range \"\\u{2129}\" \"\\u{2129}\") (re.range \"\\u{212e}\" \"\\u{212e}\") (re.range \"\\u{213a}\" \"\\u{213b}\") (re.range \"\\u{2140}\" \"\\u{2144}\") (re.range \"\\u{214a}\" \"\\u{214d}\") (re.range \"\\u{214f}\" \"\\u{215f}\") (re.range \"\\u{2189}\" \"\\u{24b5}\") (re.range \"\\u{24ea}\" \"\\u{2bff}\") (re.range \"\\u{2c2f}\" \"\\u{2c2f}\") (re.range \"\\u{2c5f}\" \"\\u{2c5f}\") (re.range \"\\u{2ce5}\" \"\\u{2cea}\") (re.range \"\\u{2cf4}\" \"\\u{2cff}\") (re.range \"\\u{2d26}\" \"\\u{2d26}\") (re.range \"\\u{2d28}\" \"\\u{2d2c}\") (re.range \"\\u{2d2e}\" \"\\u{2d2f}\") (re.range \"\\u{2d68}\" \"\\u{2d6e}\") (re.range \"\\u{2d70}\" \"\\u{2d7e}\") (re.range \"\\u{2d97}\" \"\\u{2d9f}\") (re.range \"\\u{2da7}\" \"\\u{2da7}\") (re.range \"\\u{2daf}\" \"\\u{2daf}\") (re.range \"\\u{2db7}\" \"\\u{2db7}\") (re.range \"\\u{2dbf}\" \"\\u{2dbf}\") (re.range \"\\u{2dc7}\" \"\\u{2dc7}\") (re.range \"\\u{2dcf}\" \"\\u{2dcf}\") (re.range \"\\u{2dd7}\" \"\\u{2dd7}\") (re.range \"\\u{2ddf}\" \"\\u{2ddf}\") (re.range \"\\u{2e00}\" \"\\u{2e2e}\") (re.range \"\\u{2e30}\" \"\\u{3004}\") (re.range \"\\u{3008}\" \"\\u{3020}\") (re.range \"\\u{3030}\" \"\\u{3030}\") (re.range \"\\u{3036}\" \"\\u{3037}\") (re.range \"\\u{303d}\" \"\\u{3040}\") (re.range \"\\u{3097}\" \"\\u{3098}\") (re.range \"\\u{309b}\" \"\\u{309c}\") (re.range \"\\u{30a0}\" \"\\u{30a0}\") (re.range \"\\u{30fb}\" \"\\u{30fb}\") (re.range \"\\u{3100}\" \"\\u{3104}\") (re.range \"\\u{312f}\" \"\\u{3130}\") (re.range \"\\u{318f}\" \"\\u{319f}\") (re.range \"\\u{31bb}\" \"\\u{31ef}\") (re.range \"\\u{3200}\" \"\\u{33ff}\") (re.range \"\\u{4db6}\" \"\\u{4dff}\") (re.range \"\\u{9ff0}\" \"\\u{9fff}\") (re.range \"\\u{a48d}\" \"\\u{a4cf}\") (re.range \"\\u{a4fe}\" \"\\u{a4ff}\") (re.range \"\\u{a60d}\" \"\\u{a60f}\") (re.range \"\\u{a62c}\" \"\\u{a63f}\") (re.range \"\\u{a673}\" \"\\u{a673}\") (re.range \"\\u{a67e}\" \"\\u{a67e}\") (re.range \"\\u{a6f2}\" \"\\u{a716}\") (re.range \"\\u{a720}\" \"\\u{a721}\") (re.range \"\\u{a789}\" \"\\u{a78a}\") (re.range \"\\u{a7af}\" \"\\u{a7af}\") (re.range \"\\u{a7b8}\" \"\\u{a7f6}\") (re.range \"\\u{a828}\" \"\\u{a83f}\") (re.range \"\\u{a874}\" \"\\u{a87f}\") (re.range \"\\u{a8c6}\" \"\\u{a8cf}\") (re.range \"\\u{a8da}\" \"\\u{a8df}\") (re.range \"\\u{a8f8}\" \"\\u{a8fa}\") (re.range \"\\u{a8fc}\" \"\\u{a8fc}\") (re.range \"\\u{a8fe}\" \"\\u{a8ff}\") (re.range \"\\u{a92e}\" \"\\u{a92f}\") (re.range \"\\u{a954}\" \"\\u{a95f}\") (re.range \"\\u{a97d}\" \"\\u{a97f}\") (re.range \"\\u{a9c1}\" \"\\u{a9ce}\") (re.range \"\\u{a9da}\" \"\\u{a9df}\") (re.range \"\\u{a9ff}\" \"\\u{a9ff}\") (re.range \"\\u{aa37}\" \"\\u{aa3f}\") (re.range \"\\u{aa4e}\" \"\\u{aa4f}\") (re.range \"\\u{aa5a}\" \"\\u{aa5f}\") (re.range \"\\u{aa77}\" \"\\u{aa79}\") (re.range \"\\u{aac3}\" \"\\u{aada}\") (re.range \"\\u{aade}\" \"\\u{aadf}\") (re.range \"\\u{aaf0}\" \"\\u{aaf1}\") (re.range \"\\u{aaf7}\" \"\\u{ab00}\") (re.range \"\\u{ab07}\" \"\\u{ab08}\") (re.range \"\\u{ab0f}\" \"\\u{ab10}\") (re.range \"\\u{ab17}\" \"\\u{ab1f}\") (re.range \"\\u{ab27}\" \"\\u{ab27}\") (re.range \"\\u{ab2f}\" \"\\u{ab2f}\") (re.range \"\\u{ab5b}\" \"\\u{ab5b}\") (re.range \"\\u{ab66}\" \"\\u{ab6f}\") (re.range \"\\u{abeb}\" \"\\u{abeb}\") (re.range \"\\u{abee}\" \"\\u{abef}\") (re.range \"\\u{abfa}\" \"\\u{abff}\") (re.range \"\\u{d7a4}\" \"\\u{d7af}\") (re.range \"\\u{d7c7}\" \"\\u{d7ca}\") (re.range \"\\u{d7fc}\" \"\\u{f8ff}\") (re.range \"\\u{fa6e}\" \"\\u{fa6f}\") (re.range \"\\u{fada}\" \"\\u{faff}\") (re.range \"\\u{fb07}\" \"\\u{fb12}\") (re.range \"\\u{fb18}\" \"\\u{fb1c}\") (re.range \"\\u{fb29}\" \"\\u{fb29}\") (re.range \"\\u{fb37}\" \"\\u{fb37}\") (re.range \"\\u{fb3d}\" \"\\u{fb3d}\") (re.range \"\\u{fb3f}\" \"\\u{fb3f}\") (re.range \"\\u{fb42}\" \"\\u{fb42}\") (re.range \"\\u{fb45}\" \"\\u{fb45}\") (re.range \"\\u{fbb2}\" \"\\u{fbd2}\") (re.range \"\\u{fd3e}\" \"\\u{fd4f}\") (re.range \"\\u{fd90}\" \"\\u{fd91}\") (re.range \"\\u{fdc8}\" \"\\u{fdef}\") (re.range \"\\u{fdfc}\" \"\\u{fdff}\") (re.range \"\\u{fe10}\" \"\\u{fe1f}\") (re.range \"\\u{fe30}\" \"\\u{fe32}\") (re.range \"\\u{fe35}\" \"\\u{fe4c}\") (re.range \"\\u{fe50}\" \"\\u{fe6f}\") (re.range \"\\u{fe75}\" \"\\u{fe75}\") (re.range \"\\u{fefd}\" \"\\u{ff0f}\") (re.range \"\\u{ff1a}\" \"\\u{ff20}\") (re.range \"\\u{ff3b}\" \"\\u{ff3e}\") (re.range \"\\u{ff40}\" \"\\u{ff40}\") (re.range \"\\u{ff5b}\" \"\\u{ff65}\") (re.range \"\\u{ffbf}\" \"\\u{ffc1}\") (re.range \"\\u{ffc8}\" \"\\u{ffc9}\") (re.range \"\\u{ffd0}\" \"\\u{ffd1}\") (re.range \"\\u{ffd8}\" \"\\u{ffd9}\") (re.range \"\\u{ffdd}\" \"\\u{ffff}\") (re.range \"\\u{1000c}\" \"\\u{1000c}\") (re.range \"\\u{10027}\" \"\\u{10027}\") (re.range \"\\u{1003b}\" \"\\u{1003b}\") (re.range \"\\u{1003e}\" \"\\u{1003e}\") (re.range \"\\u{1004e}\" \"\\u{1004f}\") (re.range \"\\u{1005e}\" \"\\u{1007f}\") (re.range \"\\u{100fb}\" \"\\u{1013f}\") (re.range \"\\u{10175}\" \"\\u{101fc}\") (re.range \"\\u{101fe}\" \"\\u{1027f}\") (re.range \"\\u{1029d}\" \"\\u{1029f}\") (re.range \"\\u{102d1}\" \"\\u{102df}\") (re.range \"\\u{102e1}\" \"\\u{102ff}\") (re.range \"\\u{10320}\" \"\\u{1032c}\") (re.range \"\\u{1034b}\" \"\\u{1034f}\") (re.range \"\\u{1037b}\" \"\\u{1037f}\") (re.range \"\\u{1039e}\" \"\\u{1039f}\") (re.range \"\\u{103c4}\" \"\\u{103c7}\") (re.range \"\\u{103d0}\" \"\\u{103d0}\") (re.range \"\\u{103d6}\" \"\\u{103ff}\") (re.range \"\\u{1049e}\" \"\\u{1049f}\") (re.range \"\\u{104aa}\" \"\\u{104af}\") (re.range \"\\u{104d4}\" \"\\u{104d7}\") (re.range \"\\u{104fc}\" \"\\u{104ff}\") (re.range \"\\u{10528}\" \"\\u{1052f}\") (re.range \"\\u{10564}\" \"\\u{105ff}\") (re.range \"\\u{10737}\" \"\\u{1073f}\") (re.range \"\\u{10756}\" \"\\u{1075f}\") (re.range \"\\u{10768}\" \"\\u{107ff}\") (re.range \"\\u{10806}\" \"\\u{10807}\") (re.range \"\\u{10809}\" \"\\u{10809}\") (re.range \"\\u{10836}\" \"\\u{10836}\") (re.range \"\\u{10839}\" \"\\u{1083b}\") (re.range \"\\u{1083d}\" \"\\u{1083e}\") (re.range \"\\u{10856}\" \"\\u{1085f}\") (re.range \"\\u{10877}\" \"\\u{1087f}\") (re.range \"\\u{1089f}\" \"\\u{108df}\") (re.range \"\\u{108f3}\" \"\\u{108f3}\") (re.range \"\\u{108f6}\" \"\\u{108ff}\") (re.range \"\\u{10916}\" \"\\u{1091f}\") (re.range \"\\u{1093a}\" \"\\u{1097f}\") (re.range \"\\u{109b8}\" \"\\u{109bd}\") (re.range \"\\u{109c0}\" \"\\u{109ff}\") (re.range \"\\u{10a04}\" \"\\u{10a04}\") (re.range \"\\u{10a07}\" \"\\u{10a0b}\") (re.range \"\\u{10a14}\" \"\\u{10a14}\") (re.range \"\\u{10a18}\" \"\\u{10a18}\") (re.range \"\\u{10a34}\" \"\\u{10a37}\") (re.range \"\\u{10a3b}\" \"\\u{10a3e}\") (re.range \"\\u{10a40}\" \"\\u{10a5f}\") (re.range \"\\u{10a7d}\" \"\\u{10a7f}\") (re.range \"\\u{10a9d}\" \"\\u{10abf}\") (re.range \"\\u{10ac8}\" \"\\u{10ac8}\") (re.range \"\\u{10ae7}\" \"\\u{10aff}\") (re.range \"\\u{10b36}\" \"\\u{10b3f}\") (re.range \"\\u{10b56}\" \"\\u{10b5f}\") (re.range \"\\u{10b73}\" \"\\u{10b7f}\") (re.range \"\\u{10b92}\" \"\\u{10bff}\") (re.range \"\\u{10c49}\" \"\\u{10c7f}\") (re.range \"\\u{10cb3}\" \"\\u{10cbf}\") (re.range \"\\u{10cf3}\" \"\\u{10fff}\") (re.range \"\\u{11047}\" \"\\u{11065}\") (re.range \"\\u{11070}\" \"\\u{1107e}\") (re.range \"\\u{110bb}\" \"\\u{110cf}\") (re.range \"\\u{110e9}\" \"\\u{110ef}\") (re.range \"\\u{110fa}\" \"\\u{110ff}\") (re.range \"\\u{11135}\" \"\\u{11135}\") (re.range \"\\u{11140}\" \"\\u{1114f}\") (re.range \"\\u{11174}\" \"\\u{11175}\") (re.range \"\\u{11177}\" \"\\u{1117f}\") (re.range \"\\u{111c5}\" \"\\u{111c9}\") (re.range \"\\u{111cd}\" \"\\u{111cf}\") (re.range \"\\u{111db}\" \"\\u{111db}\") (re.range \"\\u{111dd}\" \"\\u{111ff}\") (re.range \"\\u{11212}\" \"\\u{11212}\") (re.range \"\\u{11238}\" \"\\u{1123d}\") (re.range \"\\u{1123f}\" \"\\u{1127f}\") (re.range \"\\u{11287}\" \"\\u{11287}\") (re.range \"\\u{11289}\" \"\\u{11289}\") (re.range \"\\u{1128e}\" \"\\u{1128e}\") (re.range \"\\u{1129e}\" \"\\u{1129e}\") (re.range \"\\u{112a9}\" \"\\u{112af}\") (re.range \"\\u{112eb}\" \"\\u{112ef}\") (re.range \"\\u{112fa}\" \"\\u{112ff}\") (re.range \"\\u{11304}\" \"\\u{11304}\") (re.range \"\\u{1130d}\" \"\\u{1130e}\") (re.range \"\\u{11311}\" \"\\u{11312}\") (re.range \"\\u{11329}\" \"\\u{11329}\") (re.range \"\\u{11331}\" \"\\u{11331}\") (re.range \"\\u{11334}\" \"\\u{11334}\") (re.range \"\\u{1133a}\" \"\\u{1133b}\") (re.range \"\\u{11345}\" \"\\u{11346}\") (re.range \"\\u{11349}\" \"\\u{1134a}\") (re.range \"\\u{1134e}\" \"\\u{1134f}\") (re.range \"\\u{11351}\" \"\\u{11356}\") (re.range \"\\u{11358}\" \"\\u{1135c}\") (re.range \"\\u{11364}\" \"\\u{11365}\") (re.range \"\\u{1136d}\" \"\\u{1136f}\") (re.range \"\\u{11375}\" \"\\u{113ff}\") (re.range \"\\u{1144b}\" \"\\u{1144f}\") (re.range \"\\u{1145a}\" \"\\u{1147f}\") (re.range \"\\u{114c6}\" \"\\u{114c6}\") (re.range \"\\u{114c8}\" \"\\u{114cf}\") (re.range \"\\u{114da}\" \"\\u{1157f}\") (re.range \"\\u{115b6}\" \"\\u{115b7}\") (re.range \"\\u{115c1}\" \"\\u{115d7}\") (re.range \"\\u{115de}\" \"\\u{115ff}\") (re.range \"\\u{11641}\" \"\\u{11643}\") (re.range \"\\u{11645}\" \"\\u{1164f}\") (re.range \"\\u{1165a}\" \"\\u{1167f}\") (re.range \"\\u{116b8}\" \"\\u{116bf}\") (re.range \"\\u{116ca}\" \"\\u{116ff}\") (re.range \"\\u{1171a}\" \"\\u{1171c}\") (re.range \"\\u{1172c}\" \"\\u{1172f}\") (re.range \"\\u{1173a}\" \"\\u{1189f}\") (re.range \"\\u{118ea}\" \"\\u{118fe}\") (re.range \"\\u{11900}\" \"\\u{119ff}\") (re.range \"\\u{11a3f}\" \"\\u{11a46}\") (re.range \"\\u{11a48}\" \"\\u{11a4f}\") (re.range \"\\u{11a84}\" \"\\u{11a85}\") (re.range \"\\u{11a9a}\" \"\\u{11abf}\") (re.range \"\\u{11af9}\" \"\\u{11bff}\") (re.range \"\\u{11c09}\" \"\\u{11c09}\") (re.range \"\\u{11c37}\" \"\\u{11c37}\") (re.range \"\\u{11c41}\" \"\\u{11c4f}\") (re.range \"\\u{11c5a}\" \"\\u{11c71}\") (re.range \"\\u{11c90}\" \"\\u{11c91}\") (re.range \"\\u{11ca8}\" \"\\u{11ca8}\") (re.range \"\\u{11cb7}\" \"\\u{11cff}\") (re.range \"\\u{11d07}\" \"\\u{11d07}\") (re.range \"\\u{11d0a}\" \"\\u{11d0a}\") (re.range \"\\u{11d37}\" \"\\u{11d39}\") (re.range \"\\u{11d3b}\" \"\\u{11d3b}\") (re.range \"\\u{11d3e}\" \"\\u{11d3e}\") (re.range \"\\u{11d48}\" \"\\u{11d4f}\") (re.range \"\\u{11d5a}\" \"\\u{11fff}\") (re.range \"\\u{1239a}\" \"\\u{123ff}\") (re.range \"\\u{1246f}\" \"\\u{1247f}\") (re.range \"\\u{12544}\" \"\\u{12fff}\") (re.range \"\\u{1342f}\" \"\\u{143ff}\") (re.range \"\\u{14647}\" \"\\u{167ff}\") (re.range \"\\u{16a39}\" \"\\u{16a3f}\") (re.range \"\\u{16a5f}\" \"\\u{16a5f}\") (re.range \"\\u{16a6a}\" \"\\u{16acf}\") (re.range \"\\u{16aee}\" \"\\u{16aef}\") (re.range \"\\u{16af5}\" \"\\u{16aff}\") (re.range \"\\u{16b37}\" \"\\u{16b3f}\") (re.range \"\\u{16b44}\" \"\\u{16b4f}\") (re.range \"\\u{16b5a}\" \"\\u{16b62}\") (re.range \"\\u{16b78}\" \"\\u{16b7c}\") (re.range \"\\u{16b90}\" \"\\u{16eff}\") (re.range \"\\u{16f45}\" \"\\u{16f4f}\") (re.range \"\\u{16f7f}\" \"\\u{16f8e}\") (re.range \"\\u{16fa0}\" \"\\u{16fdf}\") (re.range \"\\u{16fe2}\" \"\\u{16fff}\") (re.range \"\\u{187ed}\" \"\\u{187ff}\") (re.range \"\\u{18af3}\" \"\\u{1afff}\") (re.range \"\\u{1b11f}\" \"\\u{1b16f}\") (re.range \"\\u{1b2fc}\" \"\\u{1bbff}\") (re.range \"\\u{1bc6b}\" \"\\u{1bc6f}\") (re.range \"\\u{1bc7d}\" \"\\u{1bc7f}\") (re.range \"\\u{1bc89}\" \"\\u{1bc8f}\") (re.range \"\\u{1bc9a}\" \"\\u{1bc9c}\") (re.range \"\\u{1bc9f}\" \"\\u{1d164}\") (re.range \"\\u{1d16a}\" \"\\u{1d16c}\") (re.range \"\\u{1d173}\" \"\\u{1d17a}\") (re.range \"\\u{1d183}\" \"\\u{1d184}\") (re.range \"\\u{1d18c}\" \"\\u{1d1a9}\") (re.range \"\\u{1d1ae}\" \"\\u{1d241}\") (re.range \"\\u{1d245}\" \"\\u{1d3ff}\") (re.range \"\\u{1d455}\" \"\\u{1d455}\") (re.range \"\\u{1d49d}\" \"\\u{1d49d}\") (re.range \"\\u{1d4a0}\" \"\\u{1d4a1}\") (re.range \"\\u{1d4a3}\" \"\\u{1d4a4}\") (re.range \"\\u{1d4a7}\" \"\\u{1d4a8}\") (re.range \"\\u{1d4ad}\" \"\\u{1d4ad}\") (re.range \"\\u{1d4ba}\" \"\\u{1d4ba}\") (re.range \"\\u{1d4bc}\" \"\\u{1d4bc}\") (re.range \"\\u{1d4c4}\" \"\\u{1d4c4}\") (re.range \"\\u{1d506}\" \"\\u{1d506}\") (re.range \"\\u{1d50b}\" \"\\u{1d50c}\") (re.range \"\\u{1d515}\" \"\\u{1d515}\") (re.range \"\\u{1d51d}\" \"\\u{1d51d}\") (re.range \"\\u{1d53a}\" \"\\u{1d53a}\") (re.range \"\\u{1d53f}\" \"\\u{1d53f}\") (re.range \"\\u{1d545}\" \"\\u{1d545}\") (re.range \"\\u{1d547}\" \"\\u{1d549}\") (re.range \"\\u{1d551}\" \"\\u{1d551}\") (re.range \"\\u{1d6a6}\" \"\\u{1d6a7}\") (re.range \"\\u{1d6c1}\" \"\\u{1d6c1}\") (re.range \"\\u{1d6db}\" \"\\u{1d6db}\") (re.range \"\\u{1d6fb}\" \"\\u{1d6fb}\") (re.range \"\\u{1d715}\" \"\\u{1d715}\") (re.range \"\\u{1d735}\" \"\\u{1d735}\") (re.range \"\\u{1d74f}\" \"\\u{1d74f}\") (re.range \"\\u{1d76f}\" \"\\u{1d76f}\") (re.range \"\\u{1d789}\" \"\\u{1d789}\") (re.range \"\\u{1d7a9}\" \"\\u{1d7a9}\") (re.range \"\\u{1d7c3}\" \"\\u{1d7c3}\") (re.range \"\\u{1d7cc}\" \"\\u{1d7cd}\") (re.range \"\\u{1d800}\" \"\\u{1d9ff}\") (re.range \"\\u{1da37}\" \"\\u{1da3a}\") (re.range \"\\u{1da6d}\" \"\\u{1da74}\") (re.range \"\\u{1da76}\" \"\\u{1da83}\") (re.range \"\\u{1da85}\" \"\\u{1da9a}\") (re.range \"\\u{1daa0}\" \"\\u{1daa0}\") (re.range \"\\u{1dab0}\" \"\\u{1dfff}\") (re.range \"\\u{1e007}\" \"\\u{1e007}\") (re.range \"\\u{1e019}\" \"\\u{1e01a}\") (re.range \"\\u{1e022}\" \"\\u{1e022}\") (re.range \"\\u{1e025}\" \"\\u{1e025}\") (re.range \"\\u{1e02b}\" \"\\u{1e7ff}\") (re.range \"\\u{1e8c5}\" \"\\u{1e8cf}\") (re.range \"\\u{1e8d7}\" \"\\u{1e8ff}\") (re.range \"\\u{1e94b}\" \"\\u{1e94f}\") (re.range \"\\u{1e95a}\" \"\\u{1edff}\") (re.range \"\\u{1ee04}\" \"\\u{1ee04}\") (re.range \"\\u{1ee20}\" \"\\u{1ee20}\") (re.range \"\\u{1ee23}\" \"\\u{1ee23}\") (re.range \"\\u{1ee25}\" \"\\u{1ee26}\") (re.range \"\\u{1ee28}\" \"\\u{1ee28}\") (re.range \"\\u{1ee33}\" \"\\u{1ee33}\") (re.range \"\\u{1ee38}\" \"\\u{1ee38}\") (re.range \"\\u{1ee3a}\" \"\\u{1ee3a}\") (re.range \"\\u{1ee3c}\" \"\\u{1ee41}\") (re.range \"\\u{1ee43}\" \"\\u{1ee46}\") (re.range \"\\u{1ee48}\" \"\\u{1ee48}\") (re.range \"\\u{1ee4a}\" \"\\u{1ee4a}\") (re.range \"\\u{1ee4c}\" \"\\u{1ee4c}\") (re.range \"\\u{1ee50}\" \"\\u{1ee50}\") (re.range \"\\u{1ee53}\" \"\\u{1ee53}\") (re.range \"\\u{1ee55}\" \"\\u{1ee56}\") (re.range \"\\u{1ee58}\" \"\\u{1ee58}\") (re.range \"\\u{1ee5a}\" \"\\u{1ee5a}\") (re.range \"\\u{1ee5c}\" \"\\u{1ee5c}\") (re.range \"\\u{1ee5e}\" \"\\u{1ee5e}\") (re.range \"\\u{1ee60}\" \"\\u{1ee60}\") (re.range \"\\u{1ee63}\" \"\\u{1ee63}\") (re.range \"\\u{1ee65}\" \"\\u{1ee66}\") (re.range \"\\u{1ee6b}\" \"\\u{1ee6b}\") (re.range \"\\u{1ee73}\" \"\\u{1ee73}\") (re.range \"\\u{1ee78}\" \"\\u{1ee78}\") (re.range \"\\u{1ee7d}\" \"\\u{1ee7d}\") (re.range \"\\u{1ee7f}\" \"\\u{1ee7f}\") (re.range \"\\u{1ee8a}\" \"\\u{1ee8a}\") (re.range \"\\u{1ee9c}\" \"\\u{1eea0}\") (re.range \"\\u{1eea4}\" \"\\u{1eea4}\") (re.range \"\\u{1eeaa}\" \"\\u{1eeaa}\") (re.range \"\\u{1eebc}\" \"\\u{1f12f}\") (re.range \"\\u{1f14a}\" \"\\u{1f14f}\") (re.range \"\\u{1f16a}\" \"\\u{1f16f}\") (re.range \"\\u{1f18a}\" \"\\u{1ffff}\") (re.range \"\\u{2a6d7}\" \"\\u{2a6ff}\") (re.range \"\\u{2b735}\" \"\\u{2b73f}\") (re.range \"\\u{2b81e}\" \"\\u{2b81f}\") (re.range \"\\u{2cea2}\" \"\\u{2ceaf}\") (re.range \"\\u{2ebe1}\" \"\\u{2f7ff}\") (re.range \"\\u{2fa1e}\" \"\\u{e00ff}\") (re.range \"\\u{e01f0}\" \"\\u{10fffe}\"))";
    private static String escapeChars = "(re.union (re.range \"\\u{09}\" \"\\u{0d}\") (re.range \"\\u{20}\" \"\\u{20}\") (re.range \"\\u{85}\" \"\\u{85}\") (re.range \"\\u{a0}\" \"\\u{a0}\") (re.range \"\\u{1680}\" \"\\u{1680}\") (re.range \"\\u{2000}\" \"\\u{200a}\") (re.range \"\\u{2028}\" \"\\u{2029}\") (re.range \"\\u{202f}\" \"\\u{202f}\") (re.range \"\\u{205f}\" \"\\u{205f}\") (re.range \"\\u{3000}\" \"\\u{3000}\"))";
    private static String notEscapeChars = "(re.union (re.range \"\\u{00}\" \"\\u{08}\") (re.range \"\\u{0e}\" \"\\u{1f}\") (re.range \"\\u{21}\" \"\\u{84}\") (re.range \"\\u{86}\" \"\\u{9f}\") (re.range \"\\u{a1}\" \"\\u{167f}\") (re.range \"\\u{1681}\" \"\\u{1fff}\") (re.range \"\\u{200b}\" \"\\u{2027}\") (re.range \"\\u{202a}\" \"\\u{202e}\") (re.range \"\\u{2030}\" \"\\u{205e}\") (re.range \"\\u{2060}\" \"\\u{2fff}\") (re.range \"\\u{3001}\" \"\\u{10fffe}\"))";
    private static String digitChars = "(re.union (re.range \"\\u{30}\" \"\\u{39}\") (re.range \"\\u{660}\" \"\\u{669}\") (re.range \"\\u{6f0}\" \"\\u{6f9}\") (re.range \"\\u{7c0}\" \"\\u{7c9}\") (re.range \"\\u{966}\" \"\\u{96f}\") (re.range \"\\u{9e6}\" \"\\u{9ef}\") (re.range \"\\u{a66}\" \"\\u{a6f}\") (re.range \"\\u{ae6}\" \"\\u{aef}\") (re.range \"\\u{b66}\" \"\\u{b6f}\") (re.range \"\\u{be6}\" \"\\u{bef}\") (re.range \"\\u{c66}\" \"\\u{c6f}\") (re.range \"\\u{ce6}\" \"\\u{cef}\") (re.range \"\\u{d66}\" \"\\u{d6f}\") (re.range \"\\u{de6}\" \"\\u{def}\") (re.range \"\\u{e50}\" \"\\u{e59}\") (re.range \"\\u{ed0}\" \"\\u{ed9}\") (re.range \"\\u{f20}\" \"\\u{f29}\") (re.range \"\\u{1040}\" \"\\u{1049}\") (re.range \"\\u{1090}\" \"\\u{1099}\") (re.range \"\\u{17e0}\" \"\\u{17e9}\") (re.range \"\\u{1810}\" \"\\u{1819}\") (re.range \"\\u{1946}\" \"\\u{194f}\") (re.range \"\\u{19d0}\" \"\\u{19d9}\") (re.range \"\\u{1a80}\" \"\\u{1a89}\") (re.range \"\\u{1a90}\" \"\\u{1a99}\") (re.range \"\\u{1b50}\" \"\\u{1b59}\") (re.range \"\\u{1bb0}\" \"\\u{1bb9}\") (re.range \"\\u{1c40}\" \"\\u{1c49}\") (re.range \"\\u{1c50}\" \"\\u{1c59}\") (re.range \"\\u{a620}\" \"\\u{a629}\") (re.range \"\\u{a8d0}\" \"\\u{a8d9}\") (re.range \"\\u{a900}\" \"\\u{a909}\") (re.range \"\\u{a9d0}\" \"\\u{a9d9}\") (re.range \"\\u{a9f0}\" \"\\u{a9f9}\") (re.range \"\\u{aa50}\" \"\\u{aa59}\") (re.range \"\\u{abf0}\" \"\\u{abf9}\") (re.range \"\\u{ff10}\" \"\\u{ff19}\") (re.range \"\\u{104a0}\" \"\\u{104a9}\") (re.range \"\\u{11066}\" \"\\u{1106f}\") (re.range \"\\u{110f0}\" \"\\u{110f9}\") (re.range \"\\u{11136}\" \"\\u{1113f}\") (re.range \"\\u{111d0}\" \"\\u{111d9}\") (re.range \"\\u{112f0}\" \"\\u{112f9}\") (re.range \"\\u{11450}\" \"\\u{11459}\") (re.range \"\\u{114d0}\" \"\\u{114d9}\") (re.range \"\\u{11650}\" \"\\u{11659}\") (re.range \"\\u{116c0}\" \"\\u{116c9}\") (re.range \"\\u{11730}\" \"\\u{11739}\") (re.range \"\\u{118e0}\" \"\\u{118e9}\") (re.range \"\\u{11c50}\" \"\\u{11c59}\") (re.range \"\\u{11d50}\" \"\\u{11d59}\") (re.range \"\\u{16a60}\" \"\\u{16a69}\") (re.range \"\\u{16b50}\" \"\\u{16b59}\") (re.range \"\\u{1d7ce}\" \"\\u{1d7ff}\") (re.range \"\\u{1e950}\" \"\\u{1e959}\"))";
    private static String notDigitChars = "(re.union (re.range \"\\u{00}\" \"\\u{2f}\") (re.range \"\\u{3a}\" \"\\u{65f}\") (re.range \"\\u{66a}\" \"\\u{6ef}\") (re.range \"\\u{6fa}\" \"\\u{7bf}\") (re.range \"\\u{7ca}\" \"\\u{965}\") (re.range \"\\u{970}\" \"\\u{9e5}\") (re.range \"\\u{9f0}\" \"\\u{a65}\") (re.range \"\\u{a70}\" \"\\u{ae5}\") (re.range \"\\u{af0}\" \"\\u{b65}\") (re.range \"\\u{b70}\" \"\\u{be5}\") (re.range \"\\u{bf0}\" \"\\u{c65}\") (re.range \"\\u{c70}\" \"\\u{ce5}\") (re.range \"\\u{cf0}\" \"\\u{d65}\") (re.range \"\\u{d70}\" \"\\u{de5}\") (re.range \"\\u{df0}\" \"\\u{e4f}\") (re.range \"\\u{e5a}\" \"\\u{ecf}\") (re.range \"\\u{eda}\" \"\\u{f1f}\") (re.range \"\\u{f2a}\" \"\\u{103f}\") (re.range \"\\u{104a}\" \"\\u{108f}\") (re.range \"\\u{109a}\" \"\\u{17df}\") (re.range \"\\u{17ea}\" \"\\u{180f}\") (re.range \"\\u{181a}\" \"\\u{1945}\") (re.range \"\\u{1950}\" \"\\u{19cf}\") (re.range \"\\u{19da}\" \"\\u{1a7f}\") (re.range \"\\u{1a8a}\" \"\\u{1a8f}\") (re.range \"\\u{1a9a}\" \"\\u{1b4f}\") (re.range \"\\u{1b5a}\" \"\\u{1baf}\") (re.range \"\\u{1bba}\" \"\\u{1c3f}\") (re.range \"\\u{1c4a}\" \"\\u{1c4f}\") (re.range \"\\u{1c5a}\" \"\\u{a61f}\") (re.range \"\\u{a62a}\" \"\\u{a8cf}\") (re.range \"\\u{a8da}\" \"\\u{a8ff}\") (re.range \"\\u{a90a}\" \"\\u{a9cf}\") (re.range \"\\u{a9da}\" \"\\u{a9ef}\") (re.range \"\\u{a9fa}\" \"\\u{aa4f}\") (re.range \"\\u{aa5a}\" \"\\u{abef}\") (re.range \"\\u{abfa}\" \"\\u{ff0f}\") (re.range \"\\u{ff1a}\" \"\\u{1049f}\") (re.range \"\\u{104aa}\" \"\\u{11065}\") (re.range \"\\u{11070}\" \"\\u{110ef}\") (re.range \"\\u{110fa}\" \"\\u{11135}\") (re.range \"\\u{11140}\" \"\\u{111cf}\") (re.range \"\\u{111da}\" \"\\u{112ef}\") (re.range \"\\u{112fa}\" \"\\u{1144f}\") (re.range \"\\u{1145a}\" \"\\u{114cf}\") (re.range \"\\u{114da}\" \"\\u{1164f}\") (re.range \"\\u{1165a}\" \"\\u{116bf}\") (re.range \"\\u{116ca}\" \"\\u{1172f}\") (re.range \"\\u{1173a}\" \"\\u{118df}\") (re.range \"\\u{118ea}\" \"\\u{11c4f}\") (re.range \"\\u{11c5a}\" \"\\u{11d4f}\") (re.range \"\\u{11d5a}\" \"\\u{16a5f}\") (re.range \"\\u{16a6a}\" \"\\u{16b4f}\") (re.range \"\\u{16b5a}\" \"\\u{1d7cd}\") (re.range \"\\u{1d800}\" \"\\u{1e94f}\") (re.range \"\\u{1e95a}\" \"\\u{10fffe}\"))";


    public RegexTranslator(String regex, TranslationMap tmap,
                           EscapingFunction esc)
            throws
            IllegalWorkflowException, ParsingException {
        // obtain the parse tree from the regular expression an process it
        super(RegexParser.INSTANCE.parse(regex));

        // visualize parse tree in dot format
        LOGGER.debug("{}", this.parseTree.toDot());
        this.tmap = tmap;
        this.escaper = esc;
    }

    public RegexTranslator(String regex, TranslationMap tmap)
            throws
            IllegalWorkflowException, ParsingException {
        this(regex, tmap, new SmtEscape());
    }


    public String getAny() {
        if(tmap.has(ALLCHAR)) {
            return tmap.get(ALLCHAR);
        } else {
            char from = 0;
            char to = 255;
            String any = "(" + tmap.get(RANGE) + " \"" + escaper.charEscape(from) + "\"" +
                    " \"" + escaper.charEscape(to) + "\")";
            return any;
        }
    }


    public static String charClass2Smtlib(String regex) {
        Pattern pattern = Pattern.compile(regex, Pattern.UNICODE_CHARACTER_CLASS);

        int lastMatched = -1;
        String charClassInSmtlib = "";
        for (int i = 0; i < 0x10FFFF; i++) {
            String s = new String(Character.toChars(i));
            Matcher matcher = pattern.matcher(s);
            if (matcher.matches()) {
                // 打印Unicode字符和其对应的代码点
                // System.out.println(s + " " + i);
                if (lastMatched == -1) {
                    charClassInSmtlib = "(re.range " + String.format("\"\\u{%02x}\"", i);
                } else if (lastMatched + 1 == i) {
                    // do nothing
                } else {
                    charClassInSmtlib += " " + String.format("\"\\u{%02x}\"", lastMatched) + ") (re.range " + String.format("\"\\u{%02x}\"", i);
                }
                lastMatched = i;
            }
        }
        charClassInSmtlib += " " + String.format("\"\\u{%02x}\"", lastMatched) + ")";
        charClassInSmtlib = "(re.union " + charClassInSmtlib + ")";

        // System.out.println(charClassInSmtlib);

        return charClassInSmtlib;
    }

    @Override
    protected void process(ParseTreeNode n) throws ParseTreeProcessorException {

        LOGGER.debug("Handle " + n.getId() + " " + n.getRule());

        switch (n.getRule()) {

            case "root":
            case "capture":
                simpleProp(n);
                break;
            case "complement":
                if(!tmap.has(COMPLEMENT)) {
                    throw new ParseTreeProcessorException("complement not " +
                            "supported");
                }
                String comp = "(" + tmap.get(COMPLEMENT) + " " + smap.get(n
                        .getChildren().get(0)) + ")";
                smap.put(n, comp);
                break;
            case "intersection":

                if(!tmap.has(INTERSECTION)) {
                    throw new ParseTreeProcessorException("intersection not " +
                            "supported");
                }
                String isect = createBinaryExpression(tmap.get(INTERSECTION), n
                        .getChildren());
                //alt = "(assert (" + MEMBERSHIP + " v" + vid + " " + alt + " ))";
                //String salt = putVar(alt);
                smap.put(n, isect);
                break;
            case "alternation":
                if (n.getChildren().size() == 1) {
                    simpleProp(n);
                    break;
                }
                String alt = createBinaryExpression(tmap.get(UNION), n.getChildren());
                //alt = "(assert (" + MEMBERSHIP + " v" + vid + " " + alt + " ))";
                //String salt = putVar(alt);
                smap.put(n, alt);
                break;
            case "expr":
                if (n.getChildren().size() == 1) {
                    simpleProp(n);
                    break;
                }
                boolean concat = true;
                for (ParseTreeNode c : n.getChildren()) {
                    if (!c.getRule().equals("element")) {
                        concat = false;
                    }
                }
                if (concat) {
                    String sconcat = createBinaryExpression(tmap.get(CONCAT), n
                            .getChildren());
                    //sconcat = "(assert (" + MEMBERSHIP + " v" + vid + " " + sconcat + "))";
                    //String sexpr = putVar(sconcat);
                    smap.put(n, sconcat);
                }
                break;
            case "element":

                if (n.getChildren().size() == 1) {
                    simpleProp(n);
                } else if (n.getChildren().size() == 2) {

                    ParseTreeNode last = n.getChildren().get(1);
                    ParseTreeNode first = n.getChildren().get(0);

                    //LOGGER.info("FIRST " + first.getEscapedLabel() + ">> " +
                    //        first.getId() + " " + smap.get(first));
                    //LOGGER.info("LParseTree " + last.getEscapedLabel() +
                    // ">> " + last.getId() + " " + smap.get(last));


                    String lbl = last.getLabel();

                    if (last != null && last.getRule().equals("quantifier")) {
                        switch (lbl) {
                            case "*":
                                String star = "(" + tmap.get(STAR) + " " + smap
                                        .get(first) + " )";
                                //String starvar = putVar(star);
                                //smap.put(n, starvar);
                                smap.put(n,star);
                                break;
                            case "+":
                                String plus = "(" + tmap.get(PLUS) + " " + smap
                                        .get(first) + " )";
                                smap.put(n,plus);
                                break;
                            case "?":

                                if(tmap.has(OPT)) {
                                    String opt = "(" + tmap.get(OPT) + " " + smap
                                            .get(first) + " )";
                                    smap.put(n, opt);
                                } else {
                                    lbl = "{0,1}";
                                }
                                break;
                        }

                        LOGGER.debug("lbl is {}", lbl);
                        int min = -1;
                        int max = -1;
                        Pattern pattern = Pattern.compile("\\{([0-9]*),?" +
                                "([0-9]+)?\\}");
                        Matcher matcher = pattern.matcher(lbl);


                        if (matcher.matches()) {
                            //LOGGER.debug("group 1 {}", matcher.group(1));
                            //LOGGER.debug("group 2 {}", matcher.group(2));

                            String grp1 = matcher.group(1);
                            String grp2 = matcher.group(2);
                            if (grp1 != null && !grp1.isEmpty()) {
                                min = Integer.parseInt(grp1);
                            }
                            if (grp2 != null && !grp2.isEmpty()) {
                                max = Integer.parseInt(grp2);
                            }


                            //LOGGER.debug("min {}, max {}", min,max);
                            String smin = "";
                            String sran = "";

                            if (min > 0) {
                                for (int i = 1; i < min; i++) {
                                    smin += " (" + tmap.get(CONCAT) + " " + smap
                                            .get
                                            (first);
                                }
                                smin += " " + smap.get(first);
                                smin += StringUtils.repeat(")", min - 1);
                            } else if (min <= 0) {
                                smin += "(str.to_re \"\")";
                            }


                            if (max > -1) {
                                String unroll = smin;
                                for (int i = min; i < max; i++) {
                                    sran += " (" + tmap.get(UNION) + " " +
                                            unroll;
                                    unroll = " (" + tmap.get(CONCAT) + " " +
                                            this
                                            .smap.get(first) + "  " + unroll + ")";
                                }
                                sran += " " + unroll;
                                sran += StringUtils.repeat(")", max - min);
                            } else if (max <= 0) {
                                sran = " (" + tmap.get(CONCAT) + " " + smin +
                                        " (" + tmap.get(STAR) + " " + smin + " " + "))";
                            }


                            smap.put(n, sran);
                        }
                    }
                }

                break;

            case "number":
            case "letter":
            case "literal":
            case "cc_literal":
            case "shared_literal":
                String label = " (" + tmap.get(CONV) + " " + "\"" + esc(n
                        .getLabel
                        ()) + "\")";
                this.smap.put(n,label);
                break;
            case "atom":
                if(n.isLeaf()) {
                    if(n.getLabel().equals(".")) {
                        smap.put(n, getAny());
                    }
                    else if (n.getLabel().equals("\\d")) {
                        // smap.put(n, "(re.range \"0\" \"9\")");
                        smap.put(n, digitChars);
                    }
                    else if (n.getLabel().equals("\\D")) {
                        // smap.put(n, "(re.inter re.allchar (re.comp (re.range \"0\" \"9\")))");
                        // smap.put(n, "(re.inter re.allchar (re.comp "+digitCharss+"))");
                        // smap.put(n, "(re.comp "+ digitChars +")");
                        smap.put(n, notDigitChars);
                    }
                    else if (n.getLabel().equals("\\w")) {
                        // smap.put(n, "(re.union (re.range \"a\" \"z\") (re.range \"A\" \"Z\") (re.range \"0\" \"9\") (str.to.re \"_\"))");
                        smap.put(n, wordChars);
                    }
                    else if (n.getLabel().equals("\\W")) {
                        // smap.put(n, "(re.inter re.allchar (re.comp (re.union (re.range \"a\" \"z\") (re.range \"A\" \"Z\") (re.range \"0\" \"9\") (str.to.re \"_\"))))");
                        // smap.put(n, "(re.inter re.allchar (re.comp "+wordChars+"))");
                        // smap.put(n, "(re.comp "+wordChars+")");
                        smap.put(n, notWordChars);
                    }

                    else if (n.getLabel().equals("\\s")) {
                        // smap.put(n, "(re.union (str.to_re \"\\u{09}\") (str.to_re \"\\u{0a}\") (str.to_re \"\\u{0d}\") (str.to.re \" \"))");
                        smap.put(n, escapeChars);
                    }
                    else if (n.getLabel().equals("\\S")) {
                        // smap.put(n, "(re.inter re.allchar (re.comp (re.union (str.to.re \"\\u{09}\") (str.to.re \"\\u{0a}\") (str.to.re \"\\u{0d}\") (str.to.re \" \"))))");
                        // smap.put(n, "(re.inter re.allchar (re.comp "+saperateCharss+"))");
                        // smap.put(n, "(re.comp "+ escapeChars +")");
                        smap.put(n, notEscapeChars);
                    }
                } else {
                    simpleProp(n);
                }
                break;
            case "cc_atom":
                if (n.getChildren().size() == 0) {
                    if (n.getLabel().equals("\\s")) {
                        // smap.put(n, "(re.union (str.to.re \"\\u{09}\") (str.to.re \"\\u{0a}\") (str.to.re \"\\u{0d}\") (str.to.re \" \"))");
                        smap.put(n, escapeChars);
                    }
                    else if (n.getLabel().equals("\\S")) {
                        // smap.put(n, "(re.inter re.allchar (re.comp (re.union (str.to.re \"\\u{09}\") (str.to.re \"\\u{0a}\") (str.to.re \"\\u{0d}\") (str.to.re \" \"))))");
                        // smap.put(n, "(re.inter re.allchar (re.comp "+saperateCharss+"))");
                        // smap.put(n, "(re.comp "+ escapeChars +")");
                        smap.put(n, notEscapeChars);
                    }
                    else if (n.getLabel().equals("\\d")) {
                        // smap.put(n, "(re.range \"0\" \"9\")");
                        smap.put(n, digitChars);
                    }
                    else if (n.getLabel().equals("\\D")) {
                        // smap.put(n, "(re.inter re.allchar (re.comp (re.range \"0\" \"9\")))");
                        // smap.put(n, "(re.inter re.allchar (re.comp "+digitCharss+"))");
                        // smap.put(n, "(re.comp "+ digitChars +")");
                        smap.put(n, notDigitChars);
                    }
                    else if (n.getLabel().equals("\\w")) {
                        // smap.put(n, "(re.union (re.range \"a\" \"z\") (re.range \"A\" \"Z\") (re.range \"0\" \"9\") (str.to.re \"_\"))");
                        smap.put(n, wordChars);
                    }
                    else if (n.getLabel().equals("\\W")) {
                        // smap.put(n, "(re.inter re.allchar (re.comp (re.union (re.range \"a\" \"z\") (re.range \"A\" \"Z\") (re.range \"0\" \"9\") (str.to.re \"_\"))))");
                        // smap.put(n, "(re.inter re.allchar (re.comp "+wordChars+"))");
                        // smap.put(n, "(re.comp "+wordChars+")");
                        smap.put(n, notWordChars);
                    }
                } else if (n.getChildren().size() == 1) {
                    simpleProp(n);
                } else {
                    assert(n.getChildren().size() == 2);
                    ParseTreeNode first = n.getChildren().get(0);
                    ParseTreeNode lParseTree = n.getChildren().get(1);
                    String rex = "(" + tmap.get(RANGE) + " \"" + esc(first
                            .getLabel())
                            + "\" \"" + esc(lParseTree.getLabel()) + "\")";
                    smap.put(n, rex);
                }
                break;
            case "character_class":
                if (n.getChildren().size() == 1) {
                    simpleProp(n);
                } else {
                    String cc = "";
                    int i = 0;
                    for(i = 0; i < n.getChildren().size() - 1; i++) {
                        ParseTreeNode c = n.getChildren().get(i);
                        cc += " (" + tmap.get(UNION) + " " + this.smap.get(c);
                    }
                    cc += " " + this.smap.get(n.getChildren().get(i));
                    cc += StringUtils.repeat(")", n.getChildren().size()-1);
                    // 如果n的label第二位是^，则取反
                    if (n.getLabel().charAt(1) == '^') {
                        cc = "(re.comp " + cc + ")";
                    }
                    smap.put(n, cc);
                }
                break;
        }

    }

    private String esc(String s) {
        return escaper.escape(s);
    }

    @Override
    public String getResult() {
        //LOGGER.info(debug());
        return getRootEntry();
    }

    @Override
    public String getVariables() {
        return "";
    }


}
