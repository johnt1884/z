// ==UserScript==
// @name         Twitter/X Embedder (inline error message)
// @namespace    Violentmonkey Scripts
// @match        *://*/*
// @grant        GM_xmlhttpRequest
// @connect      publish.x.com
// @version      1.9
// @author       -
// @description  Embed tweets, avoid duplicates, show error inline with URL.
// ==/UserScript==

(function () {
    'use strict';

    const tweetRegex = /(https?:\/\/(?:twitter|x)\.com\/[a-zA-Z0-9_]+\/status\/[0-9]+)/g;
    const tweetCache = new Map();
    const embeddedTweets = new Set();

    function getTweetEmbed(url, callback) {
        if (tweetCache.has(url)) {
            callback(tweetCache.get(url));
            return;
        }

        const embedUrl = `https://publish.x.com/oembed?url=${encodeURIComponent(url)}`;

        GM_xmlhttpRequest({
            method: "GET",
            url: embedUrl,
            onload: function (response) {
                try {
                    const data = JSON.parse(response.responseText);
                    if (data.html) {
                        tweetCache.set(url, data.html);
                        callback(data.html);
                    } else {
                        tweetCache.set(url, null);
                        callback(null);
                    }
                } catch {
                    tweetCache.set(url, null);
                    callback(null);
                }
            },
            onerror: function () {
                tweetCache.set(url, null);
                callback(null);
            }
        });
    }

    function processNode(node) {
        if (
            node.nodeType === Node.TEXT_NODE &&
            node.parentNode &&
            !['SCRIPT', 'STYLE', 'A', 'BLOCKQUOTE', 'IFRAME'].includes(node.parentNode.tagName)
        ) {
            const text = node.textContent;
            let match;
            let lastIndex = 0;
            const fragment = document.createDocumentFragment();
            let hasMatches = false;

            while ((match = tweetRegex.exec(text)) !== null) {
                hasMatches = true;
                const before = text.slice(lastIndex, match.index);
                if (before) fragment.appendChild(document.createTextNode(before));

                const tweetUrl = match[0];
                if (embeddedTweets.has(tweetUrl)) {
                    lastIndex = tweetRegex.lastIndex;
                    continue; // skip duplicates
                }
                embeddedTweets.add(tweetUrl);

                const placeholder = document.createElement('div');
                placeholder.textContent = 'Loading tweet...';
                placeholder.style.fontStyle = 'italic';
                fragment.appendChild(placeholder);

                getTweetEmbed(tweetUrl, (html) => {
                    if (!placeholder.parentNode) return;

                    if (html) {
                        const container = document.createElement('div');
                        container.innerHTML = html;

                        const script = container.querySelector('script');
                        if (script) {
                            const newScript = document.createElement('script');
                            newScript.src = script.src;
                            newScript.async = true;
                            newScript.charset = 'utf-8';
                            document.head.appendChild(newScript);
                            script.remove();
                        }

                        placeholder.replaceWith(container);
                    } else {
                        const errorSpan = document.createElement('span');
                        errorSpan.textContent = `Tweet unavailable or blocked in your region: ${tweetUrl.trim()}`;
                        errorSpan.style.color = 'red';
                        errorSpan.style.fontWeight = 'bold';
                        errorSpan.style.margin = '0';
                        errorSpan.style.padding = '0';

                        placeholder.replaceWith(errorSpan);
                    }
                });

                lastIndex = tweetRegex.lastIndex;
            }

            if (lastIndex < text.length) {
                fragment.appendChild(document.createTextNode(text.slice(lastIndex)));
            }

            if (hasMatches) {
                node.parentNode.replaceChild(fragment, node);
            }
        } else if (node.nodeType === Node.ELEMENT_NODE) {
            if (node.classList.contains('twitter-tweet')) return;
            Array.from(node.childNodes).forEach(processNode);
        }
    }

    const observer = new MutationObserver((mutations) => {
        observer.disconnect();
        try {
            mutations.forEach((mutation) => {
                mutation.addedNodes.forEach((node) => {
                    processNode(node);
                });
            });
        } finally {
            observer.observe(document.body, { childList: true, subtree: true });
        }
    });

    observer.disconnect();
    try {
        processNode(document.body);
    } finally {
        observer.observe(document.body, { childList: true, subtree: true });
    }
})();
